from __future__ import annotations

import unittest

from scripts.build_p0_relative_strain_dh_lgeom_vs_lorentz_gate import (
    build_payload,
    render_markdown,
)


class P0RelativeStrainDHLgeomVsLorentzGateTests(unittest.TestCase):
    def test_dh_identity_is_closed_but_strain_source_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dh-identity-closed-strain-source-open")
        self.assertTrue(payload["dh_identity_closed"])
        self.assertFalse(payload["lorentz_omega_alone_gives_nontrivial_dh"])
        self.assertTrue(payload["strain_generator_required"])
        self.assertFalse(payload["strain_generator_source_selected"])
        self.assertFalse(payload["dq_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_dh_depends_on_eta_symmetric_generator(self) -> None:
        payload = build_payload()

        self.assertIn("Gamma_alpha^dagger_eta + Gamma_alpha", payload["dh_identity"])
        self.assertIn("Sigma_alpha=1/2", payload["eta_symmetric_part"])
        self.assertIn("2 eta^{-1}", payload["dh_from_strain"])

    def test_pure_lorentz_generator_gives_zero_dh(self) -> None:
        case = build_payload()["lorentz_generator_case"]

        self.assertIn("Omega_alpha^dagger_eta=-Omega_alpha", case["condition"])
        self.assertEqual(case["consequence"], "D_alpha H=0 for D_alpha L_geom=Omega_alpha L_geom")
        self.assertIn("does not change relative strain Q", case["meaning"])

    def test_implications_forbid_identifying_omega_with_strain_by_hand(self) -> None:
        text = " ".join(build_payload()["implications"])

        self.assertIn("source-derived eta-symmetric strain generator", text)
        self.assertIn("same K/Q_cross map", text)
        self.assertIn("do not identify Omega_alpha with the strain generator", text)
        self.assertIn("do not fit Sigma_alpha", text)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("L_geom vs Lorentz", markdown)
        self.assertIn("D H identity closed: True", markdown)
        self.assertIn("Strain generator source selected: False", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
