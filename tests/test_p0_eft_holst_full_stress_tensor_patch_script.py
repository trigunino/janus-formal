from __future__ import annotations

import unittest

from scripts.build_p0_eft_holst_full_stress_tensor_patch import build_payload


class P0EFTHolstFullStressTensorPatchTests(unittest.TestCase):
    def test_full_stress_tensor_patch_is_present(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "holst-full-stress-tensor-patch-audited")
        self.assertTrue(payload["stress_tensor_patch_complete"])
        self.assertTrue(payload["legacy_source_terms_decoupled"])
        self.assertTrue(payload["coherent_activation_path_present"])

    def test_patch_not_claimed_as_planck_accepted(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["camb_patch_activated"])
        self.assertFalse(payload["planck_accepted"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
