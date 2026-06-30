from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_metric_potential_promotion_gate import build_payload


class P0MetricPotentialPromotionGateTests(unittest.TestCase):
    def test_gate_defined_but_promotion_blocked(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["metric_potential_promotion_gate_defined"])
        self.assertTrue(decision["weak_field_scalar_diagnostic_available"])
        self.assertTrue(decision["poisson_potential_promotable_for_restricted_comoving_scalar_branch"])
        self.assertFalse(decision["poisson_potential_promotable_to_metric_potential"])
        self.assertFalse(payload["prediction_ready"])

    def test_gate_reads_linearized_gauge_and_source_checks(self) -> None:
        checks = build_payload()["checks"]

        self.assertTrue(checks["linearized_00_poisson_normalization_checked"])
        self.assertFalse(checks["janus_linearized_field_equation_derived"])
        self.assertTrue(checks["gauge_branch_declared"])
        self.assertFalse(checks["janus_slip_equation_derived"])
        self.assertTrue(checks["comoving_source_identity_defined"])
        self.assertFalse(checks["general_source_identity_closed"])
        self.assertTrue(checks["restricted_comoving_scalar_closure_candidate_passed"])
        self.assertTrue(checks["restricted_branch_promotes_poisson_to_metric"])

    def test_requirements_block_short_promotion(self) -> None:
        requirements = " ".join(build_payload()["promotion_requirements"])

        self.assertIn("not only Poisson-normalized", requirements)
        self.assertIn("not only zero-Pi scalar branch", requirements)
        self.assertIn("source identity closed", requirements)
        self.assertIn("Q_det/Q_cross provenance", requirements)


if __name__ == "__main__":
    unittest.main()
