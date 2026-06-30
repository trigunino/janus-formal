from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_integrability_mirror_gate import (
    build_payload,
    render_markdown,
)


class P0BianchiMinimalIntegrabilityMirrorGateTests(unittest.TestCase):
    def test_gate_depends_on_joint_branch_but_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "integrability-mirror-gate-open")
        self.assertEqual(payload["depends_on"], "p0_bianchi_minimal_joint_dl_dlogb_solution")
        self.assertTrue(payload["local_flow_solution_available"])
        self.assertFalse(payload["full_connection_lift_closed"])
        self.assertFalse(payload["curvature_integrability_closed"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertFalse(payload["same_l_qcross_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_gates_cover_lift_curvature_mirror_and_qcross(self) -> None:
        names = {row["gate"] for row in build_payload()["gates"]}

        self.assertIn("flow_lift", names)
        self.assertIn("full_connection_lift", names)
        self.assertIn("curvature_integrability", names)
        self.assertIn("mirror_inverse", names)
        self.assertIn("same_l_qcross", names)

    def test_required_equations_are_explicit(self) -> None:
        equations = " ".join(build_payload()["required_equations"])

        self.assertIn("Omega_alpha_AB=-Omega_alpha_BA", equations)
        self.assertIn("D_alpha L=Omega_alpha L", equations)
        self.assertIn("relative curvature obstruction", equations)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", equations)
        self.assertIn("Omega_inverse_alpha", equations)

    def test_markdown_renders_non_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Full connection lift closed: False", markdown)
        self.assertIn("Curvature integrability closed: False", markdown)
        self.assertIn("Mirror inverse closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
