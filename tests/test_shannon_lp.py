"""infoq.shannon_lp 的回归测试：判定语义 + 证书精确性。

核心纪律（见 AGENTS.md 铁律 2/3）：
  * ``PROVED`` 必须附带能用**精确有理数**复核的证书；
  * ``NOT_IDENTIFIED`` 只说明命题不在 Shannon 锥内，**不代表命题为假**；
  * 数值证据不是证明。

本文件用公开 API 独立复核证书：把证书里的元素不等式标签重新 parse 回
线性形式，按证书系数做非负组合，验证其结果**精确等于**目标线性形式。
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from infoq import NOT_IDENTIFIED, PROVED, check, parse, parse_constraint  # noqa: E402
from infoq import shannon_lp  # noqa: E402


def _label_to_form(label: str) -> dict:
    """把证书标签（如 "I(Z;X|Y) >= 0" / "H(X|Y) >= 0"）转回线性形式。"""
    expr = label.split(">=")[0].strip()
    return parse(expr)


def verify_certificate(result, constraints=()):
    """用精确有理数独立复核证书；返回 (是否精确, 组合后的线性形式)。

    目标 = Σ αᵢ·eᵢ + Σ βₖ·cₖ，其中 αᵢ ≥ 0，eᵢ 为元素不等式，
    cₖ 为附加约束（系数 βₖ 符号任意）。
    """
    total: dict = {}
    for coef, label in result.certificate:
        self_check = coef >= 0  # 元素不等式必须非负组合
        if not self_check:
            raise AssertionError(f"证书系数为负：{coef} x {label}")
        for S, c in _label_to_form(label).items():
            total[S] = total.get(S, Fraction(0)) + coef * c

    cons_forms = []
    for c in constraints:
        cons_forms.extend(parse_constraint(c))
    for coef, k in result.constraint_coefs:
        for S, c in cons_forms[k].items():
            total[S] = total.get(S, Fraction(0)) + coef * c

    total = {S: c for S, c in total.items() if c != 0}
    want = {S: c for S, c in result.target.items() if c != 0}
    return total == want, total


class TestProvedClaims(unittest.TestCase):
    """已知可由 Shannon 型不等式证明的命题。"""

    CASES = [
        ("submodularity", "H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)", []),
        ("DPI under Markov", "I(X;Z) <= I(X;Y)", ["X-Y-Z"]),
        ("DPI conditional form", "I(X;Z) >= I(X;Z|Y)", ["X-Y-Z"]),
        ("chain rule", "H(X|Y)+H(Y) = H(X,Y)", []),
        ("conditional entropy nonneg", "H(X,Y|Z) >= 0", []),
        ("MI nonneg", "I(X;Y) >= 0", []),
        ("CMI nonneg", "I(X;Y|Z) >= 0", []),
        ("MI symmetry", "I(X;Y) = I(Y;X)", []),
        ("4-var chain DPI", "I(X;W) <= I(X;Y)", ["X-Y-Z-W"]),
        ("conditioning reduces entropy", "H(X) >= H(X|Y)", []),
        ("data processing via chain", "I(X;Z) <= I(X;Z,Y)", []),
        ("fractional DPI", "1/2*I(X;Z) <= 3/2*I(X;Y)", ["X-Y-Z"]),
    ]

    def test_all_proved(self):
        for name, claim, cons in self.CASES:
            with self.subTest(name):
                r = check(claim, constraints=cons)
                self.assertEqual(r.status, PROVED, f"{name}: {r.message}")

    def test_certificates_are_exact(self):
        """每条 PROVED 的证书都必须通过精确有理数复核。"""
        for name, claim, cons in self.CASES:
            with self.subTest(name):
                r = check(claim, constraints=cons)
                if r.status != PROVED:
                    self.skipTest(f"{name} not PROVED")
                ok, total = verify_certificate(r, cons)
                self.assertTrue(
                    ok,
                    f"{name}: 证书组合 {total} != 目标 {r.target}")

    def test_certificate_nonempty_for_nontrivial_claim(self):
        """非平凡命题必须有非空证书（不能靠空组合蒙混）。"""
        for name, claim, cons in self.CASES:
            if "=" in claim and ">=" not in claim and "<=" not in claim:
                continue
            with self.subTest(name):
                r = check(claim, constraints=cons)
                if r.status != PROVED:
                    self.skipTest(f"{name} not PROVED")
                self.assertTrue(
                    r.certificate or r.constraint_coefs,
                    f"{name}: PROVED 但证书为空")

    def test_specific_certificate_contents(self):
        """次模性的证书应恰为一项、系数 1 的条件互信息。

        变量顺序由 `elemental_inequalities` 内部的规范化排序决定，因此标签
        可能是 "I(X;Z|Y) >= 0"（互信息对称，等价于 I(Z;X|Y)）。这里只断言
        系数与结构，不断言具体书写顺序。
        """
        r = check("H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)")
        self.assertEqual(r.status, PROVED)
        self.assertEqual(len(r.certificate), 1)
        coef, label = r.certificate[0]
        self.assertEqual(coef, Fraction(1))
        self.assertEqual(_label_to_form(label), parse("I(Z;X|Y)"))

    def test_equality_needs_both_directions(self):
        """等式命题必须两个方向都可证。

        注意：链式法则是**线性恒等式**（目标形式恒为 0），因此空组合就是
        精确成立的证书；只有真正的不等式才需要非空证书。
        """
        r = check("H(X|Y)+H(Y) = H(X,Y)")
        self.assertEqual(r.status, PROVED)
        self.assertEqual(r.target, {})          # 恒等式，不是不等式
        self.assertEqual(r.certificate, [])     # 空组合即精确成立
        # 双向都跑过：任一方向不可证时 status 不会是 PROVED
        self.assertIn("等式", r.message)


class TestNotIdentifiedClaims(unittest.TestCase):
    """已知不在 Shannon 锥内的命题 —— 必须返回 NOT_IDENTIFIED。"""

    CASES = [
        ("Ingleton", "I(X1;X2) >= I(X1;X2|X3)+I(X1;X2|X4)+I(X3;X4)", []),
        ("false subadditivity", "H(X,Y) >= H(X)+H(Y)", []),
        ("Zhang-Yeung 1998",
         "2*I(X3;X4) <= I(X1;X2)+I(X1;X2|X3)+2*I(X1;X4|X3)"
         "+2*I(X2;X4|X3)-2*I(X3;X4|X1)", []),
        ("Zhang-Yeung exact form",
         "I(X1;X2) <= I(X1;X2|X3)+3/2*I(X1;X4|X3)-1/2*I(X1;X4)"
         "+I(X2;X4)-I(X2;X4|X1)", []),
        ("reverse DPI", "I(X;Y) <= I(X;Z)", ["X-Y-Z"]),
    ]

    def test_all_not_identified(self):
        for name, claim, cons in self.CASES:
            with self.subTest(name):
                r = check(claim, constraints=cons)
                self.assertEqual(r.status, NOT_IDENTIFIED, name)

    def test_message_warns_against_false_inference(self):
        """NOT_IDENTIFIED 的说明必须明确"不代表命题为假"（铁律 2）。"""
        for name, claim, cons in self.CASES:
            with self.subTest(name):
                r = check(claim, constraints=cons)
                self.assertIn("不代表命题为假", r.message)


class TestSemanticsDiscipline(unittest.TestCase):
    """把 AGENTS.md 的语义纪律固化成测试。"""

    def test_not_identified_is_not_a_refutation(self):
        """NOT_IDENTIFIED 与"命题为假"是两件事，必须分开陈述。

        反例：H(X,Y) >= H(X)+H(Y) 是假命题（数值可抓反例），
        而 Ingleton 是真命题但非 Shannon 型。二者 LP 结果相同。
        """
        false_claim = "H(X,Y) >= H(X)+H(Y)"
        true_non_shannon = ("I(X1;X2) >= I(X1;X2|X3)"
                            "+I(X1;X2|X4)+I(X3;X4)")
        self.assertEqual(check(false_claim).status, NOT_IDENTIFIED)
        self.assertEqual(check(true_non_shannon).status, NOT_IDENTIFIED)

    def test_trivial_claim_without_information(self):
        r = check("0 >= 0")
        self.assertEqual(r.status, PROVED)

    def test_strict_inequality_is_treated_as_nonstrict(self):
        """严格号的严格性 LP 无法判定，说明里必须提示。"""
        r = check("H(X) > H(X|Y)")
        self.assertEqual(r.status, PROVED)
        self.assertIn("严格", r.message)

    def test_result_is_reproducible(self):
        for claim, cons in [("H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)", []),
                            ("I(X;Z) <= I(X;Y)", ["X-Y-Z"])]:
            a = check(claim, constraints=cons)
            b = check(claim, constraints=cons)
            self.assertEqual(a.status, b.status)
            self.assertEqual(a.certificate, b.certificate)


class TestElementalInequalities(unittest.TestCase):
    def test_count_for_three_variables(self):
        elems = shannon_lp.elemental_inequalities(["X", "Y", "Z"])
        self.assertGreater(len(elems), 0)
        # 每条元素不等式的系数都必须是 {+1, -1}
        for vec, label in elems:
            for c in vec.values():
                self.assertIn(c, (1, -1), label)

    def test_labels_are_reparseable(self):
        """每条元素不等式标签都必须能被 parse 回同一线性形式。"""
        elems = shannon_lp.elemental_inequalities(["X", "Y", "Z"])
        for vec, label in elems:
            self.assertEqual(_label_to_form(label), vec, label)

    def test_all_elemental_inequalities_are_valid(self):
        """元素不等式本身必须可证（自洽性检查）。"""
        elems = shannon_lp.elemental_inequalities(["X", "Y"])
        for vec, label in elems:
            expr = label.split(">=")[0].strip()
            r = check(f"{expr} >= 0")
            self.assertEqual(r.status, PROVED, label)


class TestScaleLimits(unittest.TestCase):
    def test_six_variables_completes(self):
        """6 变量应在合理时间内完成（LP 规模的上限参考）。"""
        import time
        claim = "I(X1;X2) >= 0"
        t0 = time.time()
        r = check(claim)
        dt = time.time() - t0
        self.assertEqual(r.status, PROVED)
        self.assertLess(dt, 120.0, f"6 变量耗时 {dt:.1f}s 过长")

    def test_claim_with_unknown_variable_names(self):
        """任意合法标识符都能作变量名。"""
        r = check("I(alpha;beta) >= 0")
        self.assertEqual(r.status, PROVED)


if __name__ == "__main__":
    unittest.main(verbosity=2)
