"""infoq.converse 的回归测试：converse 证明的逐步机检。

任何一步 NOT_IDENTIFIED 即整条 converse 有洞。
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from infoq import NOT_IDENTIFIED, PROVED, check_steps, format_report  # noqa: E402


class TestConverseChecker(unittest.TestCase):
    def test_all_steps_proved(self):
        steps = [
            {"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []},
            {"claim": "I(X;Z,Y) <= I(X;Y)", "constraints": ["X-Y-Z"]},
        ]
        results = check_steps(steps)
        self.assertEqual(len(results), 2)
        for _st, r in results:
            self.assertEqual(r.status, PROVED)
        report = format_report(results)
        self.assertIn("全部 2 步都通过机检", report)

    def test_bad_step_is_flagged(self):
        """方向写反的一步必须被抓出来。"""
        steps = [
            {"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []},
            {"claim": "I(X;Z,Y) <= I(X;Y)", "constraints": ["X-Y-Z"]},
            {"claim": "I(X;Y) <= I(X;Z)", "constraints": ["X-Y-Z"]},
        ]
        report = format_report(check_steps(steps))
        self.assertIn("1/3 步未被机检验证", report)
        self.assertIn("该 converse 作为证明有洞", report)

    def test_report_marks_step_numbers_and_constraints(self):
        steps = [{"claim": "I(X;Z) <= I(X;Y)", "constraints": ["X-Y-Z"],
                  "note": "数据处理不等式"}]
        report = format_report(check_steps(steps))
        self.assertIn("Step 1:", report)
        self.assertIn("X-Y-Z", report)
        self.assertIn("note: 数据处理不等式", report)

    def test_notes_are_optional(self):
        steps = [{"claim": "I(X;Y) >= 0", "constraints": []}]
        report = format_report(check_steps(steps))
        self.assertNotIn("note:", report)

    def test_empty_step_list(self):
        self.assertEqual(format_report([]).strip(),
                         "结论: 全部 0 步都通过机检"
                         "（但语义是否与原命题一致仍需人工确认）。")

    def test_semantic_caveat_is_always_stated(self):
        """机检通过也不等于语义正确，报告必须保留这句告诫。"""
        steps = [{"claim": "I(X;Y) >= 0", "constraints": []}]
        report = format_report(check_steps(steps))
        self.assertIn("语义是否与原命题一致仍需人工确认", report)


if __name__ == "__main__":
    unittest.main(verbosity=2)
