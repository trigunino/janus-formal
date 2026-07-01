from __future__ import annotations

import unittest

from scripts.build_p0_eft_drag_epoch_e2_excess_carriers import build_payload


class P0EFTDragEpochE2ExcessCarriersTests(unittest.TestCase):
    def test_carrier_diagnostic_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "drag-epoch-e2-excess-carriers-scored")
        self.assertGreater(payload["required_fractional_E2_excess"], 0.0)
        self.assertGreater(payload["delta_Neff_radiation_dominated_equivalent"], 0.0)

    def test_homogeneous_a6_spin_is_not_a_natural_carrier(self) -> None:
        payload = build_payload()

        self.assertLess(payload["xi_spin_drag_required"], payload["natural_projection_floor"])
        self.assertFalse(payload["spin_a6_as_natural_homogeneous_carrier_viable"])
        self.assertEqual(payload["preferred_carrier"], "radiation_like_holst_plasma_excess")


if __name__ == "__main__":
    unittest.main()
