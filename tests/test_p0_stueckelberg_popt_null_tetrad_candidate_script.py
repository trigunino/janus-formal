from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_popt_null_tetrad_candidate import build_payload


class P0PoptNullTetradCandidateTests(unittest.TestCase):
    def test_popt_candidate_constructed_but_not_prediction_ready(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["popt_candidate_constructed"])
        self.assertEqual(decision["acceptance_tests_pass"], "partial")
        self.assertFalse(decision["source_derived_lensing_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidate_has_no_free_parameters_and_uses_same_transport(self) -> None:
        payload = build_payload()
        candidate = payload["candidate"]
        tests = {row["name"]: row for row in payload["tests"]}

        self.assertEqual(candidate["free_parameters"], [])
        self.assertTrue(tests["same_transport"]["passes"])
        self.assertTrue(tests["no_scalar_fit"]["passes"])

    def test_lensing_law_remains_open(self) -> None:
        payload = build_payload()
        tests = {row["name"]: row for row in payload["tests"]}

        self.assertFalse(tests["physical_lensing_law"]["passes"])
        self.assertIn("Sachs/optical equation", tests["physical_lensing_law"]["reason"])


if __name__ == "__main__":
    unittest.main()
