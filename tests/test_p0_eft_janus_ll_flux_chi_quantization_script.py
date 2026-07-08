import unittest

from scripts.build_p0_eft_janus_ll_flux_chi_quantization_gate import build_payload


class JanusLLFluxChiQuantizationTests(unittest.TestCase):
    def test_flux_equations_exist_but_chi_not_selected(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertIn("ll_tension", payload["equations"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])
        self.assertFalse(payload["requirements"]["q_LL_charge_unit_derived"])

    def test_remaining_object_is_ll_gauge_action(self):
        payload = build_payload()

        self.assertEqual(
            payload["best_remaining_non_rustine_object"],
            "derive_minimal_LL_gauge_action_L_of_F2_with_charge_unit",
        )


if __name__ == "__main__":
    unittest.main()
