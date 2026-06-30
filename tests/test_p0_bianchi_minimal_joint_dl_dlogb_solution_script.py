from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_joint_dl_dlogb_solution import (
    build_payload,
    render_markdown,
)


class P0BianchiMinimalJointDLDlogBSolutionTests(unittest.TestCase):
    def test_branch_is_joint_bianchi_progress_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-joint-branch-open")
        self.assertTrue(payload["starts_from_janus_bianchi"])
        self.assertTrue(payload["joint_system_written"])
        self.assertTrue(payload["u_dot_dlogb_selected"])
        self.assertTrue(payload["omega_u_u_projected_selected"])
        self.assertFalse(payload["full_dlogb_gradient_selected"])
        self.assertFalse(payload["full_omega_alpha_selected"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_split_longitudinal_and_transverse_residuals(self) -> None:
        text = " ".join(row["name"] + row["formula"] + row["role"] for row in build_payload()["equations"])

        self.assertIn("D_mu(B rho u^mu u^nu)", text)
        self.assertIn("D_mu(rho u^mu)+rho u^mu D_mu log B=0", text)
        self.assertIn("h^nu_alpha", text)
        self.assertIn("Omega_u u", text)
        self.assertIn("C^alpha_{beta gamma}", text)

    def test_minimal_generator_is_boost_only_and_no_fit(self) -> None:
        payload = build_payload()
        equations = " ".join(row["formula"] for row in payload["equations"])
        rules = " ".join(payload["no_rustine_rules"])

        self.assertIn("Omega_u_min", equations)
        self.assertIn("a_req=-h C(u,u)", equations)
        self.assertIn("not by lensing data", rules)
        self.assertIn("not by scalar calibration", rules)
        self.assertIn("cannot absorb", rules)

    def test_closure_obligations_keep_remaining_gaps_visible(self) -> None:
        obligations = " ".join(build_payload()["closure_obligations"])

        self.assertIn("connection difference", obligations)
        self.assertIn("mirror reciprocity", obligations)
        self.assertIn("integrability D_alpha L=Omega_alpha L", obligations)
        self.assertIn("same L", obligations)
        self.assertIn("pressure/Pi", obligations)
        self.assertIn("double counting", obligations)

    def test_markdown_renders_false_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("u.D log B selected: True", markdown)
        self.assertIn("Projected Omega_u u selected: True", markdown)
        self.assertIn("Full Omega_alpha selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
