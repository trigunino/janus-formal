from __future__ import annotations

import unittest

from scripts.build_p0_eft_early_deficit_carriers import build_payload


class P0EFTEarlyDeficitCarriersTests(unittest.TestCase):
    def test_deficit_carrier_audit_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "early-deficit-carriers-scored")
        self.assertGreater(payload["delta_neff_missing"], 0.0)
        self.assertGreater(payload["equivalent_pre_drag_Geff_boost"], 1.0)

    def test_carriers_are_targets_not_derivations(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["torsion_vector_carrier_plausible"])
        self.assertTrue(payload["immirzi_geff_carrier_plausible"])
        self.assertFalse(payload["is_derived_geometry"])


if __name__ == "__main__":
    unittest.main()
