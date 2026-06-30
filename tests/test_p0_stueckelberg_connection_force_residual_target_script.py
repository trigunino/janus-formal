from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_connection_force_residual_target import build_payload


class P0StueckelbergConnectionForceResidualTargetTests(unittest.TestCase):
    def test_connection_force_is_localized_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "connection-force-residual-open")
        self.assertTrue(payload["connection_force_residual_localized"])
        self.assertFalse(payload["connection_force_residual_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_sector_connection_terms_are_recorded(self) -> None:
        terms = " ".join(row["term"] for row in build_payload()["residual_force_terms"])

        self.assertIn("C_plus-minus", terms)
        self.assertIn("rho_minus", terms)
        self.assertIn("u_{-to+}", terms)
        self.assertIn("C_minus-plus", terms)
        self.assertIn("rho_plus", terms)
        self.assertIn("u_{+to-}", terms)

    def test_cancellations_require_same_map_and_pressure_reinsert(self) -> None:
        requirements = " ".join(build_payload()["required_cancellations"])

        self.assertIn("same Janus map", requirements)
        self.assertIn("Stueckelberg map-equation force", requirements)
        self.assertIn("mirror sign", requirements)
        self.assertIn("pressure/Pi", requirements)


if __name__ == "__main__":
    unittest.main()
