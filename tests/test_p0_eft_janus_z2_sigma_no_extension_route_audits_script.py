import unittest

from scripts.derive_p0_eft_janus_z2_sigma_aps_pin_projected_charge_selection_audit_gate import (
    build_payload as build_aps_charge,
)
from scripts.derive_p0_eft_janus_z2_sigma_collar_reduction_surface_intrinsic_curvature_no_extension_gate import (
    build_payload as build_collar,
)
from scripts.derive_p0_eft_janus_z2_sigma_regular_throat_radius_condition_audit_gate import (
    build_payload as build_regular_throat,
)


class JanusZ2SigmaNoExtensionRouteAuditsTest(unittest.TestCase):
    def test_collar_finds_operator_not_coefficient(self):
        payload = build_collar()
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["checks"]["surface_intrinsic_Rh_generated_by_formal_reduction"])
        self.assertFalse(payload["checks"]["coefficient_fixed_by_existing_action_alone"])
        self.assertFalse(payload["R_Sigma_solution_certificate_ready"])

    def test_regular_throat_is_scale_invariant(self):
        payload = build_regular_throat()
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["derivable"]["parity_of_h_ab_under_normal_reflection"])
        self.assertFalse(payload["derivable"]["absolute_R_Sigma_value"])
        self.assertFalse(payload["R_Sigma_solution_certificate_ready"])

    def test_aps_pin_does_not_select_absolute_charge(self):
        payload = build_aps_charge()
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["aps_pin_can_fix"]["allowed_charge_parity_or_integrality_class"])
        self.assertTrue(
            payload["aps_pin_cannot_fix_without_state_input"][
                "absolute_projected_baryon_Noether_charge"
            ]
        )
        self.assertFalse(payload["projected_charge_solution_ready"])


if __name__ == "__main__":
    unittest.main()
