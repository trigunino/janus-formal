from __future__ import annotations

import unittest

from scripts.build_p0_janus_matter_eos_pi_branch_decision import build_payload, render_markdown


class P0JanusMatterEosPiBranchDecisionTests(unittest.TestCase):
    def test_branches_are_explicit(self) -> None:
        branches = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertIn("dust", branches)
        self.assertIn("perfect_fluid", branches)
        self.assertIn("anisotropic_stress", branches)
        self.assertIn("p=0", branches["dust"]["assumption"])
        self.assertIn("p=w rho", branches["perfect_fluid"]["assumption"])

    def test_dust_is_conditional_not_general_proof(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["dust_branch_conditionally_available"])
        self.assertFalse(payload["dust_branch_general_matter_proof"])
        self.assertTrue(payload["g0i_dust_beta_inversion_available"])
        self.assertTrue(payload["eos_pi_source_audit_available"])
        self.assertTrue(payload["conditional_dust_branch_contract_available"])
        self.assertTrue(payload["kinetic_moment_eos_pi_closure_target_available"])
        self.assertTrue(payload["kinetic_moment_hierarchy_equations_available"])
        self.assertTrue(payload["kinetic_closure_routes_decision_available"])
        self.assertTrue(payload["full_vlasov_moment_closure_contract_available"])
        self.assertTrue(payload["pi_zero_preservation_gate_available"])
        self.assertTrue(payload["vlasov_geodesic_force_target_available"])
        self.assertTrue(payload["eos_prho_no_go_vlasov_gate_available"])

    def test_eos_and_pi_source_remain_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["perfect_fluid_eos_source_derived"])
        self.assertFalse(payload["anisotropic_pi_evolution_source_derived"])
        self.assertFalse(payload["pi_zero_source_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Perfect-fluid EOS source-derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
