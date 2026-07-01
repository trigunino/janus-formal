from __future__ import annotations

import unittest

from scripts.run_p0_eft_weyl_geometric_candidate_scan import CANDIDATES, build_candidate_payload


class P0EFTWeylGeometricCandidateScanTests(unittest.TestCase):
    def test_candidates_include_one_over_36_and_empirical(self) -> None:
        self.assertIn("one_over_36", CANDIDATES)
        self.assertIn("empirical_003", CANDIDATES)
        self.assertAlmostEqual(CANDIDATES["one_over_36"], 1.0 / 36.0)

    def test_dry_payload(self) -> None:
        payload = build_candidate_payload(execute=False)
        self.assertEqual(payload["status"], "weyl-geometric-candidate-scan-dry")
        self.assertEqual(payload["grid_size"], len(CANDIDATES))


if __name__ == "__main__":
    unittest.main()
