from __future__ import annotations

import unittest

from scripts.build_bianchi_transport_continuity_force_target import build_payload


class BianchiTransportContinuityForceTargetTests(unittest.TestCase):
    def test_target_is_written_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["transported_continuity_written"])
        self.assertTrue(payload["transported_force_written"])
        self.assertTrue(payload["d_l_terms_exposed"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_mirror_residuals_are_covered(self) -> None:
        continuity = {row["sector"]: row for row in build_payload()["transported_continuity"]}
        force = {row["sector"]: row for row in build_payload()["transported_force"]}

        self.assertIn("R_plus^mu", continuity["negative_to_positive"]["needed_for"])
        self.assertIn("R_minus^mu", continuity["positive_to_negative"]["needed_for"])
        self.assertIn("+ C^mu_{nu a}", force["negative_to_positive"]["equation"])
        self.assertIn("- C^mu_{nu a}", force["positive_to_negative"]["equation"])

    def test_d_l_terms_are_explicit_open_terms(self) -> None:
        d_l_terms = " ".join(build_payload()["d_l_terms"])

        self.assertIn("D L_minus_to_plus", d_l_terms)
        self.assertIn("D L_plus_to_minus", d_l_terms)
        self.assertIn("(D L_minus_to_plus)u_minus", d_l_terms)
        self.assertIn("(D L_plus_to_minus)u_plus", d_l_terms)

    def test_dust_geodesics_alone_are_forbidden(self) -> None:
        payload = build_payload()
        insufficiency = " ".join(payload["insufficiency"])

        self.assertFalse(payload["dust_geodesics_alone_sufficient"])
        self.assertIn("same-sector dust geodesics", insufficiency)
        self.assertIn("scalar Q_cross or Q_det", insufficiency)

    def test_proof_obligations_include_source_derivation_and_both_residuals(self) -> None:
        obligations = " ".join(build_payload()["proof_obligations"])

        self.assertIn("derive transported continuity", obligations)
        self.assertIn("derive transported force", obligations)
        self.assertIn("R_plus^mu=0", obligations)
        self.assertIn("R_minus^mu=0", obligations)


if __name__ == "__main__":
    unittest.main()
