from __future__ import annotations

import unittest

from scripts.build_lensing_qcross_audit import ROWS


class LensingQCrossAuditTests(unittest.TestCase):
    def test_tetrad_covector_map_is_target_not_admissible_now(self) -> None:
        rows = {row["name"]: row for row in ROWS}

        self.assertFalse(rows["tetrad_covector_map"]["admissible_now"])
        self.assertIn("L_minus_to_plus", rows["tetrad_covector_map"]["rule"])
        self.assertIn("u_minus_to_plus", rows["tetrad_covector_map"]["formula"])

    def test_raw_flrw_stack_remains_forbidden(self) -> None:
        rows = {row["name"]: row for row in ROWS}

        self.assertFalse(rows["raw_flrw_weight_stack"]["admissible_now"])
        self.assertEqual(rows["raw_flrw_weight_stack"]["status"], "forbidden shortcut")

    def test_raw_geometric_solder_map_is_not_admissible_transport(self) -> None:
        rows = {row["name"]: row for row in ROWS}

        self.assertFalse(rows["raw_geometric_solder_map"]["admissible_now"])
        self.assertIn("L_geom^T eta L_geom=eta", rows["raw_geometric_solder_map"]["rule"])
        self.assertIn("K_plus/K_minus", rows["raw_geometric_solder_map"]["rule"])


if __name__ == "__main__":
    unittest.main()
