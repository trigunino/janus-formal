import unittest

from scripts.build_p0_eft_janus_z2_sigma_two_sector_constants_chronology_audit_gate import (
    build_payload,
)


class TwoSectorConstantsChronologyAuditGateTests(unittest.TestCase):
    def test_records_two_sector_constants_and_chronology(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["common_chronology_parameter_declared"])
        self.assertIn("x0", payload["claims_recorded"]["common_chronology_parameter"])
        self.assertIn("c_minus", payload["claims_recorded"]["minus_constants"])
        self.assertTrue(payload["closure"]["minus_light_speed_higher_clue_recorded"])
        self.assertTrue(payload["closure"]["minus_distances_shorter_clue_recorded"])

    def test_is_diagnostic_and_does_not_close_main_branch(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["feeds_main_branch"])
        self.assertIn("does_not_close_R_Sigma_solution_certificate", payload["non_closure"])
        self.assertIn("does_not_close_transport_Bianchi", payload["non_closure"])
        self.assertIn("does_not_close_plus_spinor_data_ready", payload["non_closure"])

    def test_promotion_requires_active_derivation_not_pdf_claim(self):
        payload = build_payload()

        self.assertIn(
            "derive_sector_constant_laws_from_active_Z2Sigma_action",
            payload["next_required_if_promoted"],
        )
        self.assertIn(
            "derive_lapse_ratio_N_minus_over_N_plus_from_R_Sigma_solution",
            payload["next_required_if_promoted"],
        )


if __name__ == "__main__":
    unittest.main()
