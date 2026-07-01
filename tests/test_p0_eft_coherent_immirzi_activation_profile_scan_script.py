from __future__ import annotations

import unittest

from scripts.run_p0_eft_coherent_immirzi_activation_profile_scan import build_payload


class P0EFTCoherentImmirziActivationProfileScanTests(unittest.TestCase):
    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)

        self.assertEqual(payload["status"], "coherent-immirzi-activation-profile-scan-dry")
        self.assertGreaterEqual(len(payload["profiles"]), 4)
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
