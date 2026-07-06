from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_published_so3_bianchi_reduction_gate import (
    build_payload,
)


class PublishedSO3BianchiReductionGateScriptTests(unittest.TestCase):
    def test_gate_passes_as_reduced_sector_only(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["interaction_slots_ready"])
        self.assertTrue(payload["stationary_so3_reduced_bianchi_ready"])
        self.assertFalse(payload["generic_tensor_bianchi_ready"])
        self.assertFalse(payload["sigma_source_available"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_required_next_steps_preserve_sigma_blocker(self) -> None:
        payload = build_payload()

        self.assertIn("not Sigma junction source", payload["non_claims"])
        self.assertIn("derive active SO(3) throat embedding X_plus/X_minus(R)", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
