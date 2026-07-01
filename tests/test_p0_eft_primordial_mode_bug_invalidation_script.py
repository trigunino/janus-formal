from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_mode_bug_invalidation import build_payload


class P0EFTPrimordialModeBugInvalidationTests(unittest.TestCase):
    def test_invalidation_is_explicit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-mode-zero-amplitude-runs-invalidated")
        self.assertTrue(payload["must_rerun_before_citation"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
