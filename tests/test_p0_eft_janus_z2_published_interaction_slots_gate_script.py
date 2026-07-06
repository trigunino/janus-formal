from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_published_interaction_slots_gate import (
    build_payload,
)


class PublishedInteractionSlotsGateScriptTests(unittest.TestCase):
    def test_gate_records_slots_but_blocks_transport(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["interaction_tensor_complete_nonlinear_form_available"])
        self.assertFalse(payload["reduced_bianchi_closure_ready"])
        self.assertFalse(payload["can_transport_to_sigma"])
        self.assertEqual(
            payload["primary_blocker"],
            "full_nonlinear_interaction_tensor_or_reduced_bianchi_closure",
        )


if __name__ == "__main__":
    unittest.main()
