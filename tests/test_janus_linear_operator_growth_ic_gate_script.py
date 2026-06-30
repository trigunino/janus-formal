from __future__ import annotations

import unittest

from scripts.build_janus_linear_operator_growth_ic_gate import build_payload


class JanusLinearOperatorGrowthICGateTests(unittest.TestCase):
    def test_chain_is_written_but_not_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "bounded-derivation-open")
        self.assertTrue(payload["operator_growth_ic_chain_written"])
        self.assertFalse(payload["source_derived_operator_closed"])
        self.assertFalse(payload["ic_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_covers_operator_growth_transfer_amplitude_ic(self) -> None:
        steps = {row["step"] for row in build_payload()["chain"]}

        self.assertIn("Omega_s(a)", steps)
        self.assertIn("M(a)", steps)
        self.assertIn("G_J(a,a_i)", steps)
        self.assertIn("T_J(k,a_i)", steps)
        self.assertIn("A_J", steps)
        self.assertIn("IC equations", steps)

    def test_forbids_transfer_toys_fits_and_beta_before_l(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_substitutes"])

        self.assertIn("Lambda-CDM", forbidden)
        self.assertIn("Gaussian/lognormal/bounded", forbidden)
        self.assertIn("sigma8/S8/survey", forbidden)
        self.assertIn("Q_det", forbidden)
        self.assertIn("L_minus_to_plus", forbidden)


if __name__ == "__main__":
    unittest.main()
