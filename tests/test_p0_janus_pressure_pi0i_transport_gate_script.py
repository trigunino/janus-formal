from __future__ import annotations

import unittest

from scripts.build_p0_janus_pressure_pi0i_transport_gate import build_payload, render_markdown


class P0JanusPressurePi0iTransportGateTests(unittest.TestCase):
    def test_tensor_terms_cover_pressure_projector_and_pi0i(self) -> None:
        terms = {row["term"]: row for row in build_payload()["tensor_terms"]}

        self.assertIn("enthalpy_momentum", terms)
        self.assertIn("pressure_eos", terms)
        self.assertIn("anisotropic_momentum", terms)
        self.assertIn("projector", terms)
        self.assertIn("Pi0i", terms["anisotropic_momentum"]["formula"])
        self.assertIn("h^{AB}", terms["projector"]["formula"])

    def test_gate_forbids_scalar_absorption_and_mismatched_l(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden"])

        self.assertIn("Q_det or Q_cross", forbidden)
        self.assertIn("different L", forbidden)
        self.assertTrue(payload["same_l_for_pressure_pi_k_qcross_required"])
        self.assertTrue(payload["qdet_qcross_absorption_forbidden"])

    def test_dust_limit_only_not_general_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pressure-pi0i-transport-open")
        self.assertTrue(payload["dust_limit_available"])
        self.assertTrue(payload["perfect_fluid_pressure_transport_closed_algebraically"])
        self.assertTrue(payload["anisotropic_pi0i_transport_closed_algebraically"])
        self.assertFalse(payload["equation_of_state_source_derived"])
        self.assertFalse(payload["pi_evolution_source_derived"])
        self.assertTrue(payload["g0i_dust_beta_inversion_available"])
        self.assertTrue(payload["matter_eos_pi_branch_decision_available"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_closure_chain_requires_t0i_substitution_and_residuals(self) -> None:
        chain = " ".join(build_payload()["closure_chain"])

        self.assertIn("derive beta_i", chain)
        self.assertIn("equation-of-state", chain)
        self.assertIn("substitute T0i", chain)
        self.assertIn("R_plus=0", chain)

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Perfect-fluid pressure transport closed algebraically: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
