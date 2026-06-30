from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_same_l_qcross_gate import (
    build_payload,
    render_markdown,
)


class P0BianchiMinimalSameLQCrossGateTests(unittest.TestCase):
    def test_gate_starts_from_full_lift_and_mirror_attempt_but_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "same-l-qcross-gate-open")
        self.assertIn("p0_bianchi_minimal_full_connection_lift_system", payload["starts_from"])
        self.assertIn("p0_bianchi_minimal_mirror_inverse_attempt", payload["starts_from"])
        self.assertTrue(payload["same_l_pm_mp_required"])
        self.assertTrue(payload["same_l_as_k_transport_required"])
        self.assertTrue(payload["transported_null_covectors_required"])
        self.assertFalse(payload["full_omega_integrability_closed"])
        self.assertFalse(payload["mirror_integrability_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_compatibility_rows_bind_qcross_to_k_transport(self) -> None:
        rows = {row["gate"]: row for row in build_payload()["compatibility_rows"]}
        requirements = " ".join(row["requirement"] for row in rows.values())

        self.assertEqual(
            set(rows),
            {
                "starts_after_full_connection_lift",
                "mirror_inverse_pair",
                "same_l_for_k_transport",
                "same_null_covectors",
            },
        )
        self.assertTrue(all(not row["closed"] for row in rows.values()))
        self.assertIn("L_pm/L_mp", requirements)
        self.assertIn("K_plus and K_minus", requirements)
        self.assertIn("same transported null covectors", requirements)

    def test_optical_contraction_is_geometric_not_fitted_scalar(self) -> None:
        payload = build_payload()
        contractions = {row["name"]: row for row in payload["optical_contractions"]}
        formulas = " ".join(
            row["k_transport"] + row["k_contraction"] + row["q_cross"] + row["kind"]
            for row in contractions.values()
        )

        self.assertTrue(payload["geometric_optical_contraction_required"])
        self.assertFalse(payload["fitted_scalar_allowed"])
        self.assertEqual(set(contractions), {"plus_receives_minus", "minus_receives_plus"})
        self.assertTrue(all(not row["fitted_scalar"] for row in contractions.values()))
        self.assertIn("geometric_optical_contraction", formulas)
        self.assertIn("k_pm_C=L_pm^A_C k_plus_A", formulas)
        self.assertIn("k_mp_C=L_mp^A_C k_minus_A", formulas)
        self.assertIn("Q_cross_plus=A_pm/A_plus", formulas)
        self.assertIn("Q_cross_minus=A_mp/A_minus", formulas)

    def test_independent_optics_posthoc_qcross_and_qdet_absorption_are_forbidden(self) -> None:
        payload = build_payload()
        guardrails = {row["shortcut"]: row for row in payload["scalar_guardrails"]}
        reasons = " ".join(row["reason"] for row in guardrails.values())

        self.assertFalse(payload["independent_optical_l_allowed"])
        self.assertFalse(payload["posthoc_qcross_allowed"])
        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertEqual(
            set(guardrails),
            {
                "independent_optical_l",
                "posthoc_qcross",
                "qdet_absorption",
                "fitted_scalar_replacement",
            },
        )
        self.assertTrue(all(not row["allowed"] for row in guardrails.values()))
        self.assertIn("optical-only L", reasons)
        self.assertIn("not tuned after residual inspection", reasons)
        self.assertIn("may not hide optical or mirror residuals", reasons)

    def test_closure_requires_full_omega_mirror_and_same_covectors(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["closure_requirements"])
        markdown = render_markdown(payload)

        self.assertIn("full Omega_alpha lift selected", requirements)
        self.assertIn("curvature integrability", requirements)
        self.assertIn("mirror inverse row closed", requirements)
        self.assertIn("same transported null covectors", requirements)
        self.assertIn("no residual absorbed", requirements)
        self.assertIn("Physics closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
