from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_projected_perfect_fluid_extension import build_payload


class P0ProjectedPerfectFluidExtensionTests(unittest.TestCase):
    def test_dust_identity_does_not_close_full_fluid(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertFalse(decision["dust_identity_extends_to_full_fluid"])
        self.assertTrue(decision["pressure_transport_required"])
        self.assertTrue(decision["pi_transport_required"])
        self.assertFalse(decision["prediction_ready"])

    def test_pressure_and_pi_are_explicit_terms(self) -> None:
        payload = build_payload()
        split = " ".join(row["term"] for row in payload["fluid_split"])

        self.assertIn("p h", split)
        self.assertIn("Pi", split)

    def test_no_scalar_absorption(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["no_absorption_rules"])

        self.assertIn("Q_det", rules)
        self.assertIn("Q_cross", rules)
        self.assertIn("tensor terms", payload["decision"]["reason"])


if __name__ == "__main__":
    unittest.main()
