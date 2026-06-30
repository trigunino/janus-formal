from __future__ import annotations

import unittest

from scripts.build_p0_cold_vlasov_dust_preservation_probe import build_payload, render_markdown


class P0ColdVlasovDustPreservationProbeTests(unittest.TestCase):
    def test_single_stream_dust_is_only_conditional(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cold-vlasov-dust-preservation-conditional")
        self.assertTrue(payload["single_stream_preserves_p_zero"])
        self.assertTrue(payload["single_stream_preserves_pi_zero"])
        self.assertTrue(payload["dust_branch_closed_conditionally"])
        self.assertFalse(payload["general_dust_closure_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_two_stream_generates_pressure_and_pi(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["pressure_formula_verified"])
        self.assertIn("(u1 - u2)**2", payload["two_stream_pressure"])
        self.assertTrue(payload["multistream_generates_pressure"])
        self.assertTrue(payload["multistream_generates_pi"])
        self.assertIn("(u1 - u2)**2", " ".join(payload["two_stream_pi_diag"]))

    def test_conditions_keep_same_l_b4vol_requirement(self) -> None:
        payload = build_payload()
        text = " ".join(payload["single_stream_conditions"] + payload["failure_modes"])

        self.assertIn("same L/B4vol", text)
        self.assertIn("shell crossing", text)
        self.assertIn("multistream", text)
        self.assertTrue(payload["same_l_b4vol_still_required"])

    def test_markdown_keeps_no_general_closure(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Dust branch closed conditionally: True", markdown)
        self.assertIn("General dust closure proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
