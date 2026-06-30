from __future__ import annotations

import unittest

from scripts.build_p0_eft_observational_fsigma8_data import build_payload, extract_fsigma8_points


class P0EFTObservationalFSigma8DataTests(unittest.TestCase):
    def test_extracts_sdss_fsigma8_points(self) -> None:
        points = extract_fsigma8_points()

        self.assertGreaterEqual(len(points), 5)
        self.assertTrue(all(point["fsigma8"] > 0 for point in points))
        self.assertTrue(all(point["sigma"] > 0 for point in points))

    def test_payload_records_missing_desi(self) -> None:
        payload = build_payload()

        self.assertIn("DESI", payload["not_included"])
        self.assertEqual(payload["status"], "sdss-dr16-fsigma8-points-ready")


if __name__ == "__main__":
    unittest.main()
