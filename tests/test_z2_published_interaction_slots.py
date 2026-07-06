from __future__ import annotations

import unittest

from src.janus_lab.z2_published_interaction_slots import (
    published_interaction_slots_payload,
)


class PublishedInteractionSlotsTests(unittest.TestCase):
    def test_slots_match_active_projection(self) -> None:
        payload = published_interaction_slots_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertIn("T_minus_to_plus", payload["active_projection"])
        self.assertIn("B_minus_to_plus", payload["active_projection"])
        self.assertIn("- B_minus_to_plus", payload["equation_skeleton"]["plus"])
        self.assertIn("- B_plus_to_minus", payload["equation_skeleton"]["minus"])

    def test_bianchi_still_open(self) -> None:
        payload = published_interaction_slots_payload()

        self.assertFalse(payload["interaction_tensor_complete_nonlinear_form_available"])
        self.assertFalse(payload["sigma_source_available"])
        self.assertFalse(payload["reduced_bianchi_closure_ready"])
        self.assertFalse(payload["can_transport_to_sigma"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertIn("rho_eff collapse", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
