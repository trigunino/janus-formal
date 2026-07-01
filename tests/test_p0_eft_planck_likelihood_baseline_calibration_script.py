from __future__ import annotations

import unittest

from scripts.build_p0_eft_planck_likelihood_baseline_calibration import POINTS, build_payload


class P0EFTPlanckLikelihoodBaselineCalibrationTests(unittest.TestCase):
    def test_points_are_distinct(self) -> None:
        ref = POINTS["planck_lcdm_reference"]
        janus = POINTS["janus_cmb_working_point"]

        self.assertNotEqual(ref["omch2"], janus["omch2"])
        self.assertNotEqual(ref["nnu"], janus["nnu"])

    def test_lcdm_reference_is_only_offset_calibration(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_lcdm_compressed_parameters_as_data"])
        self.assertTrue(payload["raw_planck_likelihood_used"])
        self.assertTrue(payload["lowE_absolute_offset_is_normal"])


if __name__ == "__main__":
    unittest.main()
