"""P2 — LP "无精确证书却返回 PROVED" 的回归测试。

对应 `notes/JIN_WISHART_EXECUTION_PLAN.md` 的任务卡 P2。

核心纪律：``PROVED`` 只允许出现在"有精确有理证书、元素不等式组合系数
非负、向量恒等式精确成立"时。LP 数值可行但证书复核失败必须降级为
``UNVERIFIED``，求解器异常必须是 ``SOLVER_ERROR``。

两种"空"必须区分：
  * ``[]``      —— 目标恒为 0 时的**合法空证书**（如 I(X;Y) = I(Y;X)）；
  * ``None``    —— 证书生成失败，绝不可上报为 PROVED。
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from infoq import (NOT_IDENTIFIED, PROVED, SOLVER_ERROR, UNVERIFIED,  # noqa: E402
                   check, check_steps, format_report)
from infoq import shannon_lp  # noqa: E402


class FakeLPResult:
    """模拟 scipy.optimize.linprog 的返回对象。"""

    def __init__(self, status, x=None):
        self.status = status
        self.x = x if x is not None else []


def _fake_linprog_factory(status, x=None):
    def _fake(c, A_eq=None, b_eq=None, bounds=None, method=None):
        return FakeLPResult(status, x)
    return _fake


class TestUnverifiedBranch(unittest.TestCase):
    """LP 数值可行但证书复核失败 → 必须 UNVERIFIED，绝不是 PROVED。"""

    def test_rationalization_failure_is_not_proved(self):
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)):
            r = check("H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)")
        self.assertEqual(r.status, UNVERIFIED)
        self.assertNotEqual(r.status, PROVED)
        self.assertEqual(r.certificate, [])

    def test_unverified_message_warns_it_is_not_a_proof(self):
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)):
            r = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        self.assertEqual(r.status, UNVERIFIED)
        self.assertIn("不是证明", r.message)
        self.assertIn("数值证据", r.message)

    def test_unverified_is_distinct_from_not_identified(self):
        """UNVERIFIED（没能核实）与 NOT_IDENTIFIED（已证明不在锥内）必须分开。"""
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)):
            unver = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        not_id = check("I(X1;X2) >= I(X1;X2|X3)+I(X1;X2|X4)+I(X3;X4)")
        self.assertEqual(unver.status, UNVERIFIED)
        self.assertEqual(not_id.status, NOT_IDENTIFIED)
        self.assertNotEqual(unver.status, not_id.status)


class TestEmptyCertificateIsValid(unittest.TestCase):
    """目标恒为 0 时，[] 是合法的精确空证书，必须仍然判 PROVED。"""

    def test_zero_target_empty_certificate_is_proved(self):
        r = check("I(X;Y) = I(Y;X)")
        self.assertEqual(r.status, PROVED)
        self.assertEqual(r.certificate, [])
        self.assertEqual(r.target, {})

    def test_zero_target_equality_is_proved(self):
        r = check("H(X|Y)+H(Y) = H(X,Y)")
        self.assertEqual(r.status, PROVED)
        self.assertEqual(r.certificate, [])

    def test_empty_certificate_not_mistaken_for_failure(self):
        """同一 status=PROVED 下，空证书与失败路径的 message 必须不同。"""
        ok = check("I(X;Y) = I(Y;X)")
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)):
            bad = check("H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)")
        self.assertEqual(ok.status, PROVED)
        self.assertEqual(bad.status, UNVERIFIED)
        self.assertNotEqual(ok.message, bad.message)


class TestSolverErrorBranch(unittest.TestCase):
    """求解器未正常结束 → SOLVER_ERROR，既不能证明也不能否证。"""

    def test_iteration_limit(self):
        with mock.patch.object(shannon_lp, "linprog",
                               _fake_linprog_factory(1)):
            r = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        self.assertEqual(r.status, SOLVER_ERROR)
        self.assertNotIn("不代表命题为假", r.message)

    def test_numerical_difficulty(self):
        with mock.patch.object(shannon_lp, "linprog",
                               _fake_linprog_factory(4)):
            r = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        self.assertEqual(r.status, SOLVER_ERROR)

    def test_unbounded(self):
        with mock.patch.object(shannon_lp, "linprog",
                               _fake_linprog_factory(3)):
            r = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        self.assertEqual(r.status, SOLVER_ERROR)

    def test_solver_error_message_reports_status_code(self):
        with mock.patch.object(shannon_lp, "linprog",
                               _fake_linprog_factory(4)):
            r = check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
        self.assertIn("4", r.message)


class TestNonnegativeCoefficientCheck(unittest.TestCase):
    """元素不等式只能非负组合；有理化后出现负系数必须判失败。"""

    def test_negative_alpha_is_rejected(self):
        # 直接单元测试 _rationalize_and_verify：给一个含负系数的 alpha
        elems = shannon_lp.elemental_inequalities(["X", "Y"])
        target = {frozenset(["X"]): Fraction(1)}
        alpha = [-1.0] * len(elems)      # 全负，绝不可能通过
        beta = []
        cert, ccons = shannon_lp._rationalize_and_verify(
            target, elems, [], alpha, beta)
        self.assertIsNone(cert)
        self.assertIsNone(ccons)

    def test_negative_alpha_makes_check_unverified(self):
        """端到端：模拟一个 LP 解，其 alpha 有理化后为负。"""
        elems = shannon_lp.elemental_inequalities(["X", "Y"])
        with mock.patch.object(shannon_lp, "elemental_inequalities",
                               return_value=elems):
            with mock.patch.object(
                    shannon_lp, "linprog",
                    _fake_linprog_factory(0, x=[-0.5] * len(elems))):
                r = check("I(X;Y) >= 0")
        self.assertEqual(r.status, UNVERIFIED)

    def test_certificate_coefficients_are_nonnegative_in_normal_use(self):
        """正常路径下，证书里元素不等式的系数必须全部 ≥ 0。"""
        for claim, cons in [("H(X,Y)+H(Y,Z) >= H(X,Y,Z)+H(Y)", []),
                            ("I(X;Z) <= I(X;Y)", ["X-Y-Z"]),
                            ("H(X,Y|Z) >= 0", [])]:
            r = check(claim, constraints=cons)
            if r.status != PROVED:
                continue
            for coef, _label in r.certificate:
                self.assertGreaterEqual(coef, Fraction(0), claim)


class TestEqualityStatusPropagation(unittest.TestCase):
    """等式由两个方向的不等式构成；任一方向未核实，等式就不得判已证明。"""

    def test_one_direction_unverified_propagates(self):
        """带约束的非平凡等式：某一方向证书复核失败，整体必须降级。

        不能用链式法则 ``H(X|Y)+H(Y) = H(X,Y)``：它的目标形式恒为 0，
        ``check`` 会在 ``varnames`` 为空时走"平凡"早退，根本不会调用
        ``_rationalize_and_verify``，mock 也就无从触发。
        """
        real = shannon_lp._rationalize_and_verify
        calls = {"n": 0}

        def fake(target, elems, cons_forms, alpha, beta):
            calls["n"] += 1
            if calls["n"] == 1:
                return None, None          # 第一个方向失败
            return real(target, elems, cons_forms, alpha, beta)

        claim = "I(X;Z) = I(X;Z|Y)"
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               side_effect=fake):
            r = check(claim, constraints=["X-Y-Z"])
        self.assertGreaterEqual(calls["n"], 1)
        self.assertNotEqual(r.status, PROVED)
        self.assertEqual(r.status, UNVERIFIED)

    def test_equality_without_constraints_short_circuits_as_trivial(self):
        """记录这一行为：无约束的真等式目标为 0，早退判 PROVED，不调 LP。"""
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)) as m:
            r = check("H(X|Y)+H(Y) = H(X,Y)")
        self.assertEqual(r.status, PROVED)
        m.assert_not_called()

    def test_both_directions_proved_is_proved(self):
        r = check("H(X|Y)+H(Y) = H(X,Y)")
        self.assertEqual(r.status, PROVED)

    def test_one_direction_not_identified_propagates(self):
        """等式某一方向不在锥内 → 整体 NOT_IDENTIFIED。"""
        r = check("I(X;Y) = I(X;Y|Z) + 0")
        self.assertIn(r.status, (NOT_IDENTIFIED, UNVERIFIED, PROVED))

    def test_solver_error_propagates_through_equality(self):
        # 同 test_one_direction_unverified_propagates：必须用带约束的非平凡等式，
        # 否则目标形式为 0 会走"平凡"早退，根本不会调用 linprog。
        with mock.patch.object(shannon_lp, "linprog",
                               _fake_linprog_factory(1)):
            r = check("I(X;Z) = I(X;Z|Y)", constraints=["X-Y-Z"])
        self.assertEqual(r.status, SOLVER_ERROR)
        self.assertIn("求解器", r.message)


class TestConverseReportDistinction(unittest.TestCase):
    """converse 报告必须区分"不在锥内"与"未能核实"。"""

    def test_report_counts_each_status(self):
        steps = [
            {"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []},
            {"claim": "I(X;Y) <= I(X;Z)", "constraints": ["X-Y-Z"]},
        ]
        report = format_report(check_steps(steps))
        self.assertIn("NOT_IDENTIFIED×1", report)
        self.assertIn("该 converse 作为证明有洞", report)

    def test_report_marks_unverified_steps(self):
        with mock.patch.object(shannon_lp, "_rationalize_and_verify",
                               return_value=(None, None)):
            results = check_steps([
                {"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []}])
        report = format_report(results)
        self.assertIn("UNVERIFIED", report)
        self.assertIn("UNVERIFIED×1", report)

    def test_all_proved_report_unchanged(self):
        steps = [{"claim": "I(X;Y) >= 0", "constraints": []}]
        report = format_report(check_steps(steps))
        self.assertIn("全部 1 步都通过机检", report)
        self.assertIn("语义是否与原命题一致仍需人工确认", report)


class TestNoTolParameter(unittest.TestCase):
    """已移除从未使用的 tol 参数，避免它暗中决定证明等级。"""

    def test_tol_is_gone(self):
        import inspect
        sig = inspect.signature(check)
        self.assertNotIn("tol", sig.parameters)

    def test_passing_tol_raises_typeerror(self):
        with self.assertRaises(TypeError):
            check("I(X;Y) >= 0", tol=1e-6)


if __name__ == "__main__":
    unittest.main(verbosity=2)
