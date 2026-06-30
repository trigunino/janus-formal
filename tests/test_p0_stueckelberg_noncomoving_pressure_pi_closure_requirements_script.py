from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_noncomoving_pressure_pi_closure_requirements import build_payload


class P0NoncomovingPressurePiClosureRequirementsTests(unittest.TestCase):
    def test_requirements_are_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "requirements-open")
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(any(payload["closure_gates"].values()))

    def test_required_terms_cover_pressure_projector_pi_and_divergence(self) -> None:
        terms = " ".join(build_payload()["required_tensor_terms"])

        self.assertIn("p g^{mu nu}", terms)
        self.assertIn("h^{mu nu}", terms)
        self.assertIn("Pi^{mu nu}", terms)
        self.assertIn("T0i", terms)
        self.assertIn("equation of state", terms)
        self.assertIn("R_plus/R_minus", terms)

    def test_shortcuts_forbid_scalar_absorption(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("scalar Q_det", shortcuts)
        self.assertIn("scalar Q_cross", shortcuts)
        self.assertIn("dust closure", shortcuts)
        self.assertIn("Pi00=0", shortcuts)


if __name__ == "__main__":
    unittest.main()
