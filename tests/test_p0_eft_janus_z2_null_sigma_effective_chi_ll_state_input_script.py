import unittest

from scripts.write_p0_eft_janus_z2_null_sigma_effective_chi_ll_state_input import (
    build_payload,
)


class EffectiveChiLLStateInputScriptTests(unittest.TestCase):
    def test_valid_state_input_payload_is_non_observational(self):
        payload = build_payload(
            chi_abs_inverse_m=2.5,
            provenance="explicit_extension_state_boundary_condition",
        )

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertEqual(payload["extension_status"], "explicit_LL_brane_source")
        self.assertEqual(payload["chi_LL_abs_inverse_m"], 2.5)
        self.assertFalse(payload["observational_fit_used"])
        self.assertFalse(payload["compressed_planck_lcdm_background_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])

    def test_invalid_or_observational_provenance_is_rejected(self):
        with self.assertRaises(ValueError):
            build_payload(chi_abs_inverse_m=0.0, provenance="state")
        with self.assertRaises(ValueError):
            build_payload(chi_abs_inverse_m=1.0, provenance="BAO fit")


if __name__ == "__main__":
    unittest.main()
