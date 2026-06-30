from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_popt_reduced_sachs_candidate import build_payload


class P0PoptReducedSachsCandidateTests(unittest.TestCase):
    def test_reduced_candidate_is_diagnostic_only(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["reduced_candidate_accepted_for_diagnostic"])
        self.assertTrue(decision["screen_term_rejected_until_derived"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidate_keeps_only_null_null_source(self) -> None:
        payload = build_payload()
        candidate = payload["candidate"]

        self.assertIn("k_mu k_nu T_to", candidate["formula"])
        self.assertIn("screen term", candidate["dropped_until_derived"])
        self.assertEqual(candidate["free_parameters"], [])

    def test_janus_sign_and_full_lensing_remain_open(self) -> None:
        payload = build_payload()
        tests = {row["name"]: row for row in payload["tests"]}

        self.assertFalse(tests["janus_sign"]["passes"])
        self.assertFalse(tests["full_lensing_observable"]["passes"])


if __name__ == "__main__":
    unittest.main()
