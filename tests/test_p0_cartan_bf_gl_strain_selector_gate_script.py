from __future__ import annotations

import unittest

from scripts.build_p0_cartan_bf_gl_strain_selector_gate import (
    build_payload,
    render_markdown,
)


class P0CartanBfGlStrainSelectorGateTests(unittest.TestCase):
    def test_gate_is_conditional_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cartan-bf-gl-strain-selector-open")
        self.assertFalse(payload["selects_sigma_dh"])
        self.assertTrue(payload["selects_sigma_dh_conditionally"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertTrue(payload["integrability_required"])
        self.assertTrue(payload["ghost_gate_required"])
        self.assertTrue(payload["same_l_qcross_required"])
        self.assertFalse(payload["source_phi_sigma_found"])
        self.assertFalse(payload["prediction_ready"])

    def test_connection_decomposition_splits_omega_and_sigma(self) -> None:
        text = " ".join(build_payload()["connection_decomposition"])

        self.assertIn("Gamma_alpha = Omega_alpha + Sigma_alpha", text)
        self.assertIn("Omega_alpha^dagger_eta=-Omega_alpha", text)
        self.assertIn("Sigma_alpha^dagger_eta=Sigma_alpha", text)
        self.assertIn("D_alpha H", text)

    def test_requires_source_terms_for_lorentz_and_strain(self) -> None:
        terms = " ".join(build_payload()["required_source_terms"])

        self.assertIn("Phi_R[source Janus]", terms)
        self.assertIn("Phi_Sigma[source Janus]", terms)
        self.assertIn("N_alpha[source Janus]", terms)
        self.assertIn("same L_geom/L_Lorentz", terms)

    def test_rejection_rules_block_hand_inserted_bf_targets(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("do not insert Phi_Sigma", rules)
        self.assertIn("post-hoc constraint", rules)
        self.assertIn("ghost/stability", rules)
        self.assertIn("different L branches", rules)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Cartan BF GL Strain", markdown)
        self.assertIn("Source Phi_Sigma found: False", markdown)
        self.assertIn("Ghost gate required: True", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
