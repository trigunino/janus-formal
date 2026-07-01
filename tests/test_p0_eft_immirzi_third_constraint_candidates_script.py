from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_third_constraint_candidates import build_payload


class P0EFTImmirziThirdConstraintCandidatesTests(unittest.TestCase):
    def test_candidate_scan_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-third-constraint-candidates-scored")
        self.assertEqual(len(payload["cases"]), 2)
        self.assertTrue(payload["unique_candidate_found"])

    def test_preferred_candidate_is_not_yet_patch_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["preferred_case"]["name"], "traceless_holst_stress")
        self.assertFalse(payload["cambridge_safe_to_patch"])


if __name__ == "__main__":
    unittest.main()
