from __future__ import annotations

import unittest

from scripts.build_p0_janus_eos_prho_no_go_vlasov_gate import build_payload, render_markdown


class P0JanusEosPrhoNoGoVlasovGateTests(unittest.TestCase):
    def test_counterexamples_have_same_density_different_pressure(self) -> None:
        text = " ".join(row["moments"] for row in build_payload()["counterexamples"])

        self.assertIn("rho=rho0, P_ij=0, p=0", text)
        self.assertIn("rho=rho0, P_ij=rho0 sigma^2 delta_ij", text)

    def test_scalar_eos_is_not_implied(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["scalar_eos_prho_not_implied_by_vlasov"])
        self.assertFalse(payload["eos_prho_source_derived"])
        self.assertTrue(payload["velocity_dispersion_is_independent_moment"])
        self.assertTrue(payload["full_vlasov_replaces_scalar_eos"])

    def test_routes_forbid_fit_and_scalar_absorption(self) -> None:
        text = " ".join(build_payload()["admissible_routes"] + build_payload()["forbidden_routes"])

        self.assertIn("solve full Vlasov f", text)
        self.assertIn("do not infer p=p(rho)", text)
        self.assertIn("do not tune p(rho)", text)
        self.assertIn("Q_det or Q_cross", text)

    def test_no_fit_or_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_no_go(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Scalar EOS p(rho) not implied by Vlasov: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
