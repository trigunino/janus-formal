import unittest

from scripts.build_p0_eft_janus_z2_sigma_brown_york_boundary_charge_reduction_gate import (
    build_payload,
)


class BrownYorkBoundaryChargeReductionGateTests(unittest.TestCase):
    def test_formula_is_reduced_but_waits_for_curvature_and_measure(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            payload["charge_route"],
            "BrownYork_quasilocal_boundary_reference_subtraction",
        )
        self.assertTrue(payload["closure"]["unit_intrinsic_metric_q_ab_available"])
        self.assertTrue(payload["closure"]["G_Z2Sigma_available"])
        self.assertTrue(payload["closure"]["boundary_reference_subtraction_available"])
        self.assertTrue(payload["closure"]["k_ref_minus_k_phys_symbolic_available"])
        self.assertFalse(payload["closure"]["absolute_R_Sigma_or_surface_measure_available"])
        self.assertFalse(payload["boundary_charge_reduction_ready"])
        self.assertIn("do_not_identify_reference_zero_with_physical_charge", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
