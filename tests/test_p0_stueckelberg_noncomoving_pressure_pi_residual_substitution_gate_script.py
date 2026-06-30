from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_noncomoving_pressure_pi_residual_substitution_gate import build_payload


class P0PressurePiResidualSubstitutionGateTests(unittest.TestCase):
    def test_gate_is_open_for_both_residuals(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "residual-substitution-gate-open")
        self.assertFalse(payload["r_plus_pressure_pi_residual_closed"])
        self.assertFalse(payload["r_minus_pressure_pi_residual_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_substitutions_include_pressure_pi_and_open_derivatives(self) -> None:
        rows = build_payload()["residual_terms"]
        substitutions = " ".join(row["substitution"] for row in rows)
        open_terms = " ".join(term for row in rows for term in row["open_terms"])

        self.assertIn("(rho+p)u^mu u^nu", substitutions)
        self.assertIn("p g^{mu nu}", substitutions)
        self.assertIn("Pi^{mu nu}", substitutions)
        self.assertIn("D Pi", open_terms)
        self.assertIn("T0i momentum", open_terms)

    def test_forbids_scalar_and_t00_only_shortcuts(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("scalar Q_det", shortcuts)
        self.assertIn("scalar Q_cross", shortcuts)
        self.assertIn("T00-only", shortcuts)


if __name__ == "__main__":
    unittest.main()
