"""Regression checks for failure modes that could falsely complete a SHEAF task.

No Lean/model calls; all mutation is confined to temporary fixture directories.
"""
from copy import deepcopy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import sheaf as a


class CoordinatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        (a.PROJECT / "local").mkdir(exist_ok=True)

    def test_named_argument_does_not_truncate_target(self):
        text = 'namespace X\ntheorem t (x : Nat) : id (α := Nat) x = x := by rfl\nend X\n'
        self.assertEqual(a.statements_text(text)["X.t"], '(x : Nat) : id (α := Nat) x = x')

    def test_string_delimiters_are_ignored_by_header_balancing(self):
        body = '(s : String := "([) :=") : s = s := by rfl'
        self.assertEqual(a.complete_statement(body), '(s : String := "([) :=") : s = s')

    def test_target_drift_after_named_argument_is_rejected(self):
        lock = a.read(a.PROJECT / "locks/targets.json")
        text = a.within_root(lock["source"]).read_text(encoding="utf-8")
        changed = text.replace(' M (by norm_num))) x ≤ x := by', ' M (by norm_num))) x ≤ 2*x := by')
        self.assertNotEqual(text, changed)
        with self.assertRaisesRegex(ValueError, "LOCKED TARGET CHANGED"):
            a.validate_lock_data(lock, changed)

    def test_null_type_receipt_cannot_be_accepted(self):
        evidence = a.read(a.ROOT / 'verification/sheaf_wishart/pilot-acceptance.json')
        check_path = a.within_root(evidence['check'])
        original_read = a.read
        record = deepcopy(original_read(check_path))
        record['types'] = None
        with patch.object(a, 'read', side_effect=lambda path: record if Path(path) == check_path else original_read(path)):
            with self.assertRaisesRegex(ValueError, 'Missing leaf/type'):
                a.verify_acceptance(evidence)

    def test_timed_out_review_cannot_be_accepted(self):
        evidence = a.read(a.ROOT / 'verification/sheaf_wishart/pilot-acceptance.json')
        receipt_path = a.within_root(evidence['review']['receipt'])
        original_read = a.read
        record = deepcopy(original_read(receipt_path))
        record['exit_code'] = 124
        with patch.object(a, 'read', side_effect=lambda path: record if Path(path) == receipt_path else original_read(path)):
            with self.assertRaisesRegex(ValueError, 'No successful real P4'):
                a.verify_acceptance(evidence)

    def test_separate_run_manifest_cannot_weaken_a_target(self):
        evidence = deepcopy(a.read(a.ROOT / 'verification/sheaf_wishart/pilot-acceptance.json'))
        with tempfile.TemporaryDirectory(dir=a.PROJECT / 'local') as temporary:
            path = Path(temporary) / 'targets.json'
            lock = deepcopy(a.read(a.PROJECT / 'locks/targets.json'))
            name = next(iter(lock['statements']))
            lock['statements'][name] += ' OR True'
            a.write(path, lock)
            evidence['target_lock'] = a.rel(path)
            with self.assertRaisesRegex(ValueError, 'LOCKED TARGET CHANGED'):
                a.verify_acceptance(evidence)

    def test_separate_run_checker_must_match_its_lock(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / 'local') as temporary:
            path = Path(temporary) / 'targets.json'
            checker = Path(temporary) / 'Checker.lean'
            checker.write_text('different checker', encoding='utf-8')
            lock = deepcopy(a.read(a.PROJECT / 'locks/targets.json'))
            lock['type_check_source'] = a.rel(checker)
            a.write(path, lock)
            with self.assertRaisesRegex(ValueError, 'type-comparison source changed'):
                a.validate_locks(a.rel(path))

    def test_successful_leaf_without_main_integration_is_rejected(self):
        evidence = a.read(a.ROOT / 'verification/sheaf_wishart/pilot-acceptance.json')
        with tempfile.TemporaryDirectory(dir=a.PROJECT / 'local') as temporary:
            fake_lean = Path(temporary)
            (fake_lean / 'JinWishartFormalization.lean').write_text('import AnotherModule\n', encoding='utf-8')
            with patch.object(a, 'LEAN', fake_lean):
                with self.assertRaisesRegex(ValueError, 'Target module not imported'):
                    a.verify_acceptance(evidence)

    def test_target_hypothesis_drift_is_rejected(self):
        lock = a.read(a.PROJECT / "locks/targets.json")
        text = a.within_root(lock["source"]).read_text(encoding="utf-8")
        weakened = text.replace("(x : ℝ) (hx : 0≤x)", "(x : ℝ) (extra : x≤1) (hx : 0≤x)")
        self.assertNotEqual(text, weakened)
        with self.assertRaisesRegex(ValueError, "LOCKED TARGET CHANGED"):
            a.validate_lock_data(lock, weakened)

    def test_proof_edits_do_not_require_unlocking_targets(self):
        lock = a.read(a.PROJECT / "locks/targets.json")
        text = a.within_root(lock["source"]).read_text(encoding="utf-8")
        # A lexical test only: the real compiler still has to check the proof.
        a.validate_lock_data(lock, text.replace("  let S :=", "  -- proof comment\n  let S :="))

    def test_imported_definition_drift_is_rejected(self):
        lock = deepcopy(a.read(a.PROJECT / "locks/targets.json"))
        key = next(iter(lock["definition_dependencies"]))
        lock["definition_dependencies"][key] = "0" * 64
        with self.assertRaisesRegex(ValueError, "DEPENDENCY CHANGED"):
            a.validate_lock_data(lock)

    def test_second_process_cannot_take_a_live_claim(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            lock = Path(temporary) / "claim.lock"
            with a.exclusive(lock, "first"):
                child = subprocess.run([str(a.PYTHON), "-X", "utf8", "-c",
                    "import sys; from pathlib import Path; import sheaf; "
                    "\ntry:\n with sheaf.exclusive(Path(sys.argv[1]), 'second'): pass"
                    "\nexcept FileExistsError: raise SystemExit(3)", str(lock)],
                    cwd=Path(__file__).parent, capture_output=True, text=True)
                self.assertEqual(child.returncode, 3, child.stderr)
                self.assertEqual(a.read(lock)["group"], "first")
            self.assertFalse(lock.exists())

    def test_cleanup_never_deletes_another_owners_lock(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            lock = Path(temporary) / "claim.lock"
            with a.exclusive(lock, "first"):
                a.write(lock, dict(token="another-owner", group="second"))
            self.assertTrue(lock.exists())

    def test_missing_dependency_blocks_graph(self):
        with patch.object(a.dq, "load", return_value={
                "target": dict(id="target", target=True, proof_deps=["missing"])}):
            with self.assertRaisesRegex(ValueError, "Missing DAG dependency"):
                a.graph()

    def test_cycle_blocks_graph(self):
        with patch.object(a.dq, "load", return_value={
                "a": dict(id="a", target=True, proof_deps=["b"]),
                "b": dict(id="b", proof_deps=["a"])}):
            with self.assertRaisesRegex(ValueError, "DAG cycle"):
                a.graph()

    def test_no_sorry_does_not_mean_verified(self):
        nodes = {
            "target": dict(id="target", kind="target", target=True,
                           module="Example", proof=["Written proof"],
                           verification=dict(status="check_failed")),
            "unneeded": dict(id="unneeded", kind="statement", statement="Deferred")}
        rows = a.queue_data(a.dq.Dag(nodes))
        self.assertEqual([r["id"] for r in rows], ["target"])
        nodes["target"]["verification"]["status"] = "verified"
        with patch.object(a, "verification_current", return_value=True):
            self.assertEqual(a.queue_data(a.dq.Dag(nodes)), [])
        with patch.object(a, "verification_current", return_value=False):
            stale = a.queue_data(a.dq.Dag(nodes))
            self.assertEqual(stale[0]["kind"], "stale-evidence")

    def test_malformed_claim_cleanup_preserves_original_failure(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            lock = Path(temporary) / "claim.lock"
            with self.assertRaisesRegex(RuntimeError, "original failure"):
                with self.assertWarnsRegex(UserWarning, "Unreadable claim"):
                    with a.exclusive(lock, "first"):
                        lock.write_text("{", encoding="utf-8")
                        raise RuntimeError("original failure")
            self.assertTrue(lock.exists())

    def test_bounded_lease_closes_even_when_check_raises(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            session = Path(temporary)
            a.write(session / "state.json", dict(stage="CLOSED", checkpoint="keep"))
            with patch.object(a, "SESSION", session):
                with self.assertRaisesRegex(RuntimeError, "simulated failure"):
                    with a.lease():
                        self.assertEqual(a.read(session / "state.json")["stage"], "ACTIVE_SHEAF_BOUNDED_CHECK")
                        raise RuntimeError("simulated failure")
            state = a.read(session / "state.json")
            self.assertEqual(state["stage"], "SHEAF_BOUNDED_CHECK_FINISHED")
            self.assertEqual(state["checkpoint"], "keep")
            self.assertEqual(state["automation_status"], "PAUSED")
            self.assertNotIn("sheaf_coordinator_token", state)

    def test_existing_active_coordinator_is_not_replaced(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            session = Path(temporary)
            original = dict(stage="ACTIVE_OTHER_COORDINATOR", checkpoint="keep")
            a.write(session / "state.json", original)
            with patch.object(a, "SESSION", session):
                with self.assertRaisesRegex(ValueError, "Another active coordinator"):
                    with a.lease():
                        self.fail("Should never acquire an active coordinator lease")
            self.assertEqual(a.read(session / "state.json"), original)

    def test_existing_stop_marker_is_preserved(self):
        with tempfile.TemporaryDirectory(dir=a.PROJECT / "local") as temporary:
            session = Path(temporary)
            stop = session / "STOP"
            stop.write_text("human stop", encoding="utf-8")
            with patch.object(a, "SESSION", session):
                with self.assertRaisesRegex(ValueError, "Existing STOP"):
                    with a.lease():
                        self.fail("STOP must block a new run")
            self.assertEqual(stop.read_text(encoding="utf-8"), "human stop")


if __name__ == "__main__":
    unittest.main(verbosity=2)
