import unittest

from scripts.build_p0_eft_janus_unimodular_four_form_sector_gate import build_payload


class JanusUnimodularFourFormSectorTests(unittest.TestCase):
    def test_four_form_equations_close_but_alpha_does_not(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["equations_closed"]["four_form_constant"])
        self.assertTrue(payload["equations_closed"]["flux_quantization_formal"])
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertEqual(payload["deep_verdict"], "conditional_open_not_closed")

    def test_missing_inputs_are_janus_specific(self):
        payload = build_payload()
        missing = " ".join(payload["missing_for_no_fit"])

        self.assertIn("Janus-derived A3/F4", missing)
        self.assertIn("charge unit", missing)
        self.assertIn("primitive sector", missing)


if __name__ == "__main__":
    unittest.main()
