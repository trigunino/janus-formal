from __future__ import annotations

import unittest

from scripts.build_bianchi_ansatz_audit import build_payload


class BianchiAnsatzAuditTests(unittest.TestCase):
    def test_naive_cross_copy_is_not_closed(self) -> None:
        payload = build_payload()
        rows = {row["ansatz"]: row for row in payload["ansatz_rows"]}

        self.assertFalse(payload["physics_closed"])
        self.assertEqual(rows["naive_cross_copy"]["status"], "not closed")
        self.assertIn("C.K", rows["naive_cross_copy"]["failure"])

    def test_required_target_demands_both_residuals(self) -> None:
        payload = build_payload()
        required = " ".join(payload["required_properties"])

        self.assertIn("both R_plus^mu=0 and R_minus^mu=0", required)
        self.assertIn("Q_cross", required)
        self.assertIn("anisotropic-stress", required)


if __name__ == "__main__":
    unittest.main()
