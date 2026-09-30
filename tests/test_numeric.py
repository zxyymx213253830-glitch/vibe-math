"""infoq.numeric 的回归测试：数值反例预言机。

纪律（AGENTS.md 铁律 1/3）：先数值后证明；数值证据不是证明。
反例 = 构造性否定；紧性 = 证明路线提示；二者都不是证明。
"""
import sys
import unittest
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from infoq import Oracle, parse  # noqa: E402


class TestOracleFindsCounterexamples(unittest.TestCase):
    """已知为假的命题，预言机必须找到反例。"""

    def test_conditional_entropy_reversed_is_false(self):
        """H(Z|X,Y) >= H(Z|X) 是假的（条件越多熵越小）。"""
        orc = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=7)
        out = orc.probe(parse("H(Z|X,Y) - H(Z|X)"), n_samples=100_000)
        self.assertTrue(out["counterexample"])
        self.assertLess(out["gap"], -1e-9)

    def test_subadditivity_reversed_is_false(self):
        """H(X,Y) >= H(X)+H(Y) 是假的（独立时取等）。"""
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=7)
        out = orc.probe(parse("H(X,Y) - H(X) - H(Y)"), n_samples=100_000)
        self.assertTrue(out["counterexample"])
        # 最小间隙为 -H(X) = -ln 2
        self.assertAlmostEqual(out["gap"], -np.log(2), places=6)

    def test_counterexample_pmf_is_a_distribution(self):
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=3)
        out = orc.probe(parse("H(X,Y) - H(X) - H(Y)"), n_samples=50_000)
        pmf = out["pmf"]
        self.assertEqual(pmf.shape, (4,))
        self.assertAlmostEqual(float(pmf.sum()), 1.0, places=9)
        self.assertTrue(np.all(pmf >= -1e-15))

    def test_describe_prints_readable_table(self):
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=3)
        out = orc.probe(parse("H(X,Y) - H(X) - H(Y)"), n_samples=20_000)
        text = orc.describe(out["pmf"])
        self.assertIn("P(", text)
        self.assertIn("X=", text)


class TestOracleTightness(unittest.TestCase):
    """已知紧的不等式，最小间隙应约为 0。"""

    def test_submodularity_is_tight(self):
        orc = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=7)
        out = orc.probe(
            parse("H(X,Y)+H(Y,Z) - H(X,Y,Z) - H(Y)"), n_samples=200_000)
        self.assertTrue(out["tight"])
        self.assertGreaterEqual(out["gap"], -1e-9)

    def test_mutual_information_is_tight(self):
        """I(X;Y) >= 0，独立时取等。"""
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=11)
        out = orc.probe(parse("I(X;Y)"), n_samples=100_000)
        self.assertTrue(out["tight"])
        self.assertGreaterEqual(out["gap"], -1e-9)

    def test_conditioning_reduces_entropy_is_tight(self):
        """H(X) - H(X|Y) >= 0，X 由 Y 决定时取等。"""
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=5)
        out = orc.probe(parse("H(X) - H(X|Y)"), n_samples=100_000)
        self.assertTrue(out["tight"])


class TestOracleIsNotAProof(unittest.TestCase):
    """数值上"远离为假"不是证明（铁律 3）。"""

    def test_gap_positive_does_not_imply_proved(self):
        """这里只验证输出结构，不断言命题真伪。"""
        orc = Oracle(variables={"X", "Y"}, levels=2, seed=1)
        out = orc.probe(parse("H(X) - H(X|Y)"), n_samples=10_000)
        self.assertFalse(out["counterexample"])
        self.assertIn("tight", out)
        self.assertIn("gap", out)
        self.assertIn("samples", out)
        self.assertEqual(out["samples"], 10_000)

    def test_levels_three_supported(self):
        orc = Oracle(variables={"X", "Y"}, levels=3, seed=2)
        self.assertEqual(orc.cells, 9)
        out = orc.probe(parse("H(X) - H(X|Y)"), n_samples=20_000)
        self.assertIn("gap", out)

    def test_refine_changes_nothing_essential(self):
        form = parse("H(Z|X,Y) - H(Z|X)")
        a = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=7).probe(
            form, n_samples=20_000, refine=False)
        b = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=7).probe(
            form, n_samples=20_000, refine=True)
        self.assertTrue(a["counterexample"])
        self.assertTrue(b["counterexample"])
        self.assertLessEqual(b["gap"], a["gap"] + 1e-9)


class TestOracleDeterminism(unittest.TestCase):
    def test_same_seed_same_result(self):
        form = parse("H(Z|X,Y) - H(Z|X)")
        a = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=42).probe(
            form, n_samples=20_000)
        b = Oracle(variables={"X", "Y", "Z"}, levels=2, seed=42).probe(
            form, n_samples=20_000)
        self.assertEqual(a["gap"], b["gap"])
        np.testing.assert_allclose(a["pmf"], b["pmf"])

    def test_different_seed_still_finds_counterexample(self):
        form = parse("H(Z|X,Y) - H(Z|X)")
        for seed in range(5):
            out = Oracle(variables={"X", "Y", "Z"}, levels=2,
                         seed=seed).probe(form, n_samples=20_000)
            self.assertTrue(out["counterexample"], f"seed={seed}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
