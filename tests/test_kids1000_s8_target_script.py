from __future__ import annotations

import unittest

from scripts.build_kids1000_s8_target import JSON_PATH, build_payload, main


class KiDS1000S8TargetTests(unittest.TestCase):
    def test_kids1000_cosmic_shear_low_s8_target_is_loaded(self) -> None:
        payload = build_payload()
        target = payload["targets"][0]

        self.assertEqual(target["survey_id"], "KiDS-1000")
        self.assertEqual(target["probe"], "cosmic_shear")
        self.assertAlmostEqual(target["s8"], 0.759)
        self.assertGreater(target["pull_vs_planck2018_s8"], 2.0)

    def test_compressed_target_does_not_claim_full_likelihood(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["compressed_target_ready"])
        self.assertFalse(payload["full_survey_likelihood_ready"])
        self.assertEqual(payload["n_fit_parameters"], 0)
        self.assertIn("KiDS covariance matrix", payload["missing_for_full_likelihood"])

    def test_report_is_written(self) -> None:
        main()
        payload = __import__("json").loads(JSON_PATH.read_text(encoding="utf-8"))

        self.assertEqual(payload["status"], "compressed-s8-target-ready")
        self.assertIn("low-S8 compressed target", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
