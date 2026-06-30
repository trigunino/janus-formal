from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_source_identity_branch import build_payload


class P0SourceIdentityBranchTests(unittest.TestCase):
    def test_comoving_source_identity_partial_only(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["comoving_t00_density_check_passed"])
        self.assertTrue(decision["source_identity_defined_for_comoving_scalar_branch"])
        self.assertFalse(decision["general_source_identity_closed"])
        self.assertFalse(decision["pressure_pi_general_case_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_admissible_reduction_tracks_comoving_pi_and_q_factors(self) -> None:
        reduction = " ".join(build_payload()["admissible_reduction"].values())

        self.assertIn("comoving", reduction)
        self.assertIn("Pi00", reduction)
        self.assertIn("pressure contributes to slip", reduction)
        self.assertIn("Q_det/Q_cross", reduction)

    def test_open_cases_block_noncomoving_and_general_pressure_pi(self) -> None:
        open_cases = " ".join(build_payload()["open_cases"])

        self.assertIn("non-comoving", open_cases)
        self.assertIn("Pi00", open_cases)
        self.assertIn("pressure gradients", open_cases)
        self.assertIn("Q_det/Q_cross provenance", open_cases)


if __name__ == "__main__":
    unittest.main()
