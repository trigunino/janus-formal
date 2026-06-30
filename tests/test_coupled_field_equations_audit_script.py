from __future__ import annotations

import unittest

from scripts.build_coupled_field_equations_audit import build_payload


class CoupledFieldEquationsAuditTests(unittest.TestCase):
    def test_audit_marks_bianchi_as_open_tensor_constraint(self) -> None:
        payload = build_payload()
        rows = {row["item"]: row for row in payload["equations"]}

        self.assertEqual(rows["Bianchi closure"]["status"], "open tensor constraint")
        self.assertIn("didactic", payload["source_status"])


if __name__ == "__main__":
    unittest.main()
