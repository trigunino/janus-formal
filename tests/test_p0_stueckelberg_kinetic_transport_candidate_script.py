from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_kinetic_transport_candidate import build_payload


class P0KineticTransportCandidateTests(unittest.TestCase):
    def test_kinetic_shape_defined_but_open(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["kinetic_equation_shape_defined"])
        self.assertFalse(decision["source_derived"])
        self.assertTrue(decision["cold_limit_matches_sheet_sum"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_have_plus_minus_residuals(self) -> None:
        payload = build_payload()
        equations = " ".join(row["equation"] for row in payload["equations"])
        residuals = " ".join(row["residual"] for row in payload["equations"])

        self.assertIn("R_kin,+", equations)
        self.assertIn("R_kin,-", equations)
        self.assertIn("not fitted", residuals)

    def test_moments_include_pressure_open(self) -> None:
        payload = build_payload()
        tests = {row["name"]: row for row in payload["moment_tests"]}

        self.assertEqual(tests["first_moment"]["closed"], "conditional")
        self.assertFalse(tests["second_moment"]["closed"])
        self.assertIn("pressure", tests["second_moment"]["target"])


if __name__ == "__main__":
    unittest.main()
