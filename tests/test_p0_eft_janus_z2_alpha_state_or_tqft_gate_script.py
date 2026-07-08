import unittest

from scripts.build_p0_eft_janus_z2_alpha_state_or_tqft_gate import build_payload


class AlphaStateOrTQFTSelectionGateTests(unittest.TestCase):
    def test_alpha_is_currently_state_sector_fallback(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["selected_route"], "none")
        self.assertTrue(payload["state_sector_fallback"])
        self.assertFalse(payload["non_circular_selector_ready"])
        self.assertFalse(payload["selection_law_unique_alpha_derivable"])
        self.assertTrue(payload["alpha_state_sector_remains_required"])

    def test_forced_microcanonical_selection(self):
        payload = build_payload(force_microcanonical=True)

        self.assertTrue(payload["microcanonical_route_ready"])
        self.assertFalse(payload["tqft_route_ready"])
        self.assertEqual(payload["selected_route"], "microcanonical")

    def test_forced_tqft_selection(self):
        payload = build_payload(force_tqft=True)

        self.assertTrue(payload["tqft_route_ready"])
        self.assertFalse(payload["microcanonical_route_ready"])
        self.assertEqual(payload["selected_route"], "tqft")

    def test_ambiguous_when_both_forced(self):
        payload = build_payload(force_microcanonical=True, force_tqft=True)

        self.assertEqual(payload["selected_route"], "ambiguous")
        self.assertTrue(payload["non_circular_selector_ready"])
        self.assertFalse(payload["state_sector_fallback"])


if __name__ == "__main__":
    unittest.main()
