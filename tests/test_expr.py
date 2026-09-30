"""infoq.expr 的回归测试。

运行:
    D:\\miniconda3\\python.exe -m unittest discover -s tests -v
    (将来装了 pytest 后也可: D:\\miniconda3\\python.exe -m pytest tests -q)

重点覆盖 README / AGENTS.md 承诺的表达式语法，尤其是标量倍乘：
``2*I(X;Y)``、``3/2*H(X,Y,Z)``、``2*(H(X)+H(Y))``。
这些写法在 2026-09-26 之前会抛 ExprError（词法器收进了 ``*`` 但递归下降
parser 从未处理它），本文件即为该缺陷的回归防线。
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from infoq import ExprError, parse, parse_constraint, parse_claim, pretty  # noqa: E402


def h(*names):
    """构造 {frozenset(names): Fraction(1)}，便于与 parse 的结果比对。"""
    return {frozenset(names): Fraction(1)}


class TestParseBasics(unittest.TestCase):
    def test_single_entropy(self):
        self.assertEqual(parse("H(X)"), h("X"))

    def test_joint_entropy(self):
        self.assertEqual(parse("H(X,Y)"), h("X", "Y"))

    def test_conditional_entropy(self):
        # H(A|T) = h(A∪T) - h(T)
        self.assertEqual(parse("H(X|Y)"),
                         {frozenset(["X", "Y"]): Fraction(1),
                          frozenset(["Y"]): Fraction(-1)})

    def test_mutual_information(self):
        # I(A;B|C) = h(A∪C) + h(B∪C) - h(A∪B∪C) - h(C)
        self.assertEqual(parse("I(X;Y)"),
                         {frozenset(["X"]): Fraction(1),
                          frozenset(["Y"]): Fraction(1),
                          frozenset(["X", "Y"]): Fraction(-1)})

    def test_conditional_mutual_information(self):
        self.assertEqual(parse("I(X;Y|Z)"),
                         {frozenset(["X", "Z"]): Fraction(1),
                          frozenset(["Y", "Z"]): Fraction(1),
                          frozenset(["X", "Y", "Z"]): Fraction(-1),
                          frozenset(["Z"]): Fraction(-1)})

    def test_union_dedups_and_ignores_order(self):
        self.assertEqual(parse("H(X,Y,X)"), parse("H(Y,X)"))

    def test_zero_is_empty_form(self):
        self.assertEqual(parse("0"), {})

    def test_linear_combination(self):
        form = parse("H(X,Y,Z) + H(Y) - H(X,Y) - H(Y,Z)")
        self.assertEqual(form, {
            frozenset(["X", "Y", "Z"]): Fraction(1),
            frozenset(["Y"]): Fraction(1),
            frozenset(["X", "Y"]): Fraction(-1),
            frozenset(["Y", "Z"]): Fraction(-1),
        })

    def test_pretty_roundtrip(self):
        for s in ["H(X)", "I(X;Y)", "H(X|Y,Z)", "I(X1,X2;Y|Z)",
                  "H(X,Y) + H(Y,Z) - H(X,Y,Z) - H(Y)"]:
            self.assertEqual(parse(pretty(parse(s))), parse(s), s)


class TestScalarMultiplication(unittest.TestCase):
    """README 承诺的标量倍乘语法（2026-09-26 修复）。"""

    def test_explicit_star(self):
        self.assertEqual(parse("2*I(X;Y)"),
                         {k: 2 * v for k, v in parse("I(X;Y)").items()})

    def test_fraction_coefficient(self):
        self.assertEqual(parse("3/2*H(X,Y,Z)"),
                         {frozenset(["X", "Y", "Z"]): Fraction(3, 2)})

    def test_half_fraction(self):
        self.assertEqual(parse("1/2*H(X)"),
                         {frozenset(["X"]): Fraction(1, 2)})

    def test_readme_documented_example(self):
        """README 里的原句：2*I(X;Y) - 3/2*H(X,Y,Z) >= 0"""
        form = parse("2*I(X;Y) - 3/2*H(X,Y,Z)")
        self.assertEqual(form, {
            frozenset(["X"]): Fraction(2),
            frozenset(["Y"]): Fraction(2),
            frozenset(["X", "Y"]): Fraction(-2),
            frozenset(["X", "Y", "Z"]): Fraction(-3, 2),
        })

    def test_star_times_parenthesised_group(self):
        self.assertEqual(parse("2*(H(X)+H(Y))"),
                         {frozenset(["X"]): Fraction(2),
                          frozenset(["Y"]): Fraction(2)})

    def test_paren_scalar_coefficient(self):
        self.assertEqual(parse("(1/3)*H(X)"),
                         {frozenset(["X"]): Fraction(1, 3)})
        self.assertEqual(parse("(1/3) H(X)"),
                         {frozenset(["X"]): Fraction(1, 3)})

    def test_implicit_multiplication_still_works(self):
        """数字后直接跟原子（无 '*'）是历史支持的写法，不能回归。"""
        self.assertEqual(parse("2 I(X;Y)"), parse("2*I(X;Y)"))

    def test_coefficient_after_atom(self):
        self.assertEqual(parse("I(X;Y)*2"), parse("2*I(X;Y)"))

    def test_trailing_division(self):
        self.assertEqual(parse("H(X|Y)*2/3"),
                         {frozenset(["X", "Y"]): Fraction(2, 3),
                          frozenset(["Y"]): Fraction(-2, 3)})

    def test_spaces_around_operators(self):
        self.assertEqual(parse("2 / 3 * I(X;Y)"), parse("2/3*I(X;Y)"))
        self.assertEqual(parse("3 * H(X|Y)"), parse("3*H(X|Y)"))

    def test_chained_scalars(self):
        self.assertEqual(parse("2*3*I(X;Y)"), parse("6*I(X;Y)"))

    def test_negative_coefficient(self):
        self.assertEqual(parse("-2*I(X;Y)"),
                         {k: -2 * v for k, v in parse("I(X;Y)").items()})

    def test_two_fractional_terms(self):
        self.assertEqual(parse("(1/2)*I(X;Y) + (1/2)*I(Y;Z)"),
                         {frozenset(["X"]): Fraction(1, 2),
                          frozenset(["Y"]): Fraction(1),
                          frozenset(["Z"]): Fraction(1, 2),
                          frozenset(["X", "Y"]): Fraction(-1, 2),
                          frozenset(["Y", "Z"]): Fraction(-1, 2)})

    def test_paren_group_containing_info_quantity(self):
        self.assertEqual(parse("(H(X))*2"),
                         {frozenset(["X"]): Fraction(2)})


class TestParseRejections(unittest.TestCase):
    """非法输入必须抛 ExprError（而不是静默解析或抛别的异常）。"""

    def test_info_quantities_cannot_multiply(self):
        with self.assertRaises(ExprError):
            parse("H(X)*H(Y)")
        with self.assertRaises(ExprError):
            parse("I(X;Y)*H(X)")

    def test_nonzero_constant_term(self):
        for s in ["2", "2 + I(X;Y)", "(1/3)", "3/2"]:
            with self.assertRaises(ExprError, msg=s):
                parse(s)

    def test_trailing_star(self):
        for s in ["2*", "I(X;Y)*", "2**I(X;Y)"]:
            with self.assertRaises(ExprError, msg=s):
                parse(s)

    def test_leading_star(self):
        with self.assertRaises(ExprError):
            parse("*I(X;Y)")

    def test_division_between_info_quantities(self):
        with self.assertRaises(ExprError):
            parse("H(X)/H(Y)")

    def test_zero_denominator(self):
        for s in ["1/0*I(X;Y)", "(1/0)*H(X)"]:
            with self.assertRaises(ExprError, msg=s):
                parse(s)

    def test_slash_without_number(self):
        with self.assertRaises(ExprError):
            parse("H(X)/")

    def test_reserved_word_as_variable(self):
        with self.assertRaises(ExprError):
            parse("H(H)")
        with self.assertRaises(ExprError):
            parse("I(X;I)")

    def test_unknown_function(self):
        with self.assertRaises(ExprError):
            parse("J(X;Y)")

    def test_empty_expression(self):
        with self.assertRaises(ExprError):
            parse("")

    def test_unrecognised_character(self):
        with self.assertRaises(ExprError):
            parse("H(X) $ H(Y)")

    def test_trailing_garbage(self):
        with self.assertRaises(ExprError):
            parse("H(X) H(Y)")

    def test_error_type_is_valueerror_subclass(self):
        """ExprError 必须是 ValueError 子类，便于调用方统一捕获。"""
        self.assertTrue(issubclass(ExprError, ValueError))


class TestParseClaim(unittest.TestCase):
    def test_ge(self):
        op, l, r, lf, rf = parse_claim("I(X;Z) >= I(X;Y)")
        self.assertEqual((op, l, r), (">=", "I(X;Z)", "I(X;Y)"))
        self.assertEqual(lf, parse("I(X;Z)"))
        self.assertEqual(rf, parse("I(X;Y)"))

    def test_le(self):
        op, _, _, _, _ = parse_claim("I(X;Z) <= I(X;Y)")
        self.assertEqual(op, "<=")

    def test_equality(self):
        op, _, _, _, _ = parse_claim("H(X|Y)+H(Y) = H(X,Y)")
        self.assertEqual(op, "=")

    def test_strict(self):
        for s, want in [("H(X) > H(X|Y)", ">"), ("H(X) < H(X|Y)", "<")]:
            self.assertEqual(parse_claim(s)[0], want)

    def test_fractional_claim(self):
        op, l, r, lf, rf = parse_claim("2*I(X;Y) - 3/2*H(X,Y,Z) >= 0")
        self.assertEqual(op, ">=")
        self.assertEqual(lf, parse("2*I(X;Y) - 3/2*H(X,Y,Z)"))
        self.assertEqual(rf, {})

    def test_missing_comparator(self):
        with self.assertRaises(ExprError):
            parse_claim("I(X;Y)")


class TestParseConstraint(unittest.TestCase):
    def test_markov_chain_three(self):
        # X-Y-Z ⇒ I(X;Z|Y) = 0
        forms = parse_constraint("X-Y-Z")
        self.assertEqual(forms, [parse("I(X;Z|Y)")])

    def test_markov_chain_four(self):
        # X-Y-Z-W ⇒ 全部"隔一个条件独立"
        forms = parse_constraint("X-Y-Z-W")
        self.assertEqual(forms, [
            parse("I(X;Z|Y)"),
            parse("I(X;W|Y,Z)"),
            parse("I(Y;W|Z)"),
        ])

    def test_markov_chain_five_length(self):
        forms = parse_constraint("A-B-C-D-E")
        self.assertEqual(len(forms), 6)  # C(5,2) - 4 = 6

    def test_general_equality_constraint(self):
        forms = parse_constraint("I(X;Z|Y) = 0")
        self.assertEqual(forms, [parse("I(X;Z|Y)")])

    def test_general_equality_two_sided(self):
        forms = parse_constraint("I(X;Y) = I(X;Y|Z)")
        self.assertEqual(forms, [parse("I(X;Y) - I(X;Y|Z)")])

    def test_invalid_constraint(self):
        for s in ["X Y Z", "I(X;Y)", ""]:
            with self.assertRaises(ExprError, msg=s):
                parse_constraint(s)


if __name__ == "__main__":
    unittest.main(verbosity=2)
