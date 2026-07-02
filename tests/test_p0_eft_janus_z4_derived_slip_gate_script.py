import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_gate import build_payload


class P0EFTJanusZ4DerivedSlipGateTests(unittest.TestCase):
    def test_derived_slip_gate_contract_blocks_free_slip(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-gate")
        self.assertTrue(payload["archived_carrier_degenerate_candidate_confirmed"])
        self.assertTrue(payload["derived_slip_gate_contract_passed"])
        self.assertFalse(payload["slip_is_derived"])
        self.assertFalse(payload["slip_source_derivation_available"])
        self.assertFalse(payload["derived_slip_candidate_enabled"])
        self.assertFalse(payload["free_slip_parameter"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertTrue(payload["denominator_guarded_eta_diagnostic_only"])
        self.assertTrue(payload["lambda_zero_identity"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["no_raw_toy_LOS"])
        self.assertTrue(payload["source_level_regeneration_required"])
        self.assertTrue(payload["Bianchi_consistency_guard"])
        self.assertTrue(payload["Phi_Psi_split_consistent"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
