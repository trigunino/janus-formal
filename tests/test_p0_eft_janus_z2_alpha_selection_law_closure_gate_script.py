import unittest

from scripts.build_p0_eft_janus_z2_alpha_selection_law_closure_gate import build_payload


class AlphaSelectionLawClosureGateTests(unittest.TestCase):
    def test_no_unique_selector_is_claimed(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["unique_alpha_selector_derived"])
        self.assertTrue(payload["alpha_state_sector_remains_required"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_all_routes_have_equations_and_verdicts(self):
        payload = build_payload()

        for route in payload["selection_routes"]:
            self.assertTrue(route["selection_equation"])
            self.assertTrue(route["verdict"])
            self.assertTrue(route["reason"])

    def test_flux_and_casimir_are_not_silent_successes(self):
        payload = build_payload()
        verdicts = {route["id"]: route["verdict"] for route in payload["selection_routes"]}

        self.assertEqual(verdicts["flux_quantization"], "requires_extra_quantum_structure")
        self.assertEqual(verdicts["casimir_topology"], "requires_extra_quantum_state")


if __name__ == "__main__":
    unittest.main()
