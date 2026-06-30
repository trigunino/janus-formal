from __future__ import annotations

import unittest

from scripts.build_interaction_tensor_attempt_audit import build_payload


class InteractionTensorAttemptAuditTests(unittest.TestCase):
    def test_2025_book_is_roadmap_not_proof(self) -> None:
        payload = build_payload()

        self.assertIn("roadmap", payload["source_status"])
        self.assertIn("does not close", payload["verdict"])

    def test_dipole_repeller_branch_is_kept_as_observable_target(self) -> None:
        payload = build_payload()
        rows = {row["item"]: row for row in payload["rows"]}

        self.assertEqual(rows["dipole repeller induced geometry"]["status"], "observable-target")
        self.assertEqual(rows["strong positive-sector objects"]["status"], "not-closed")


if __name__ == "__main__":
    unittest.main()
