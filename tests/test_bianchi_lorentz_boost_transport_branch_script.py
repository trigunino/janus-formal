from __future__ import annotations

import unittest

from scripts.build_bianchi_lorentz_boost_transport_branch import (
    build_payload,
    render_markdown,
)


class BianchiLorentzBoostTransportBranchTests(unittest.TestCase):
    def test_dust_stress_and_lorentz_transport_are_recorded(self) -> None:
        payload = build_payload()
        setup = " ".join(payload["setup"])
        transport = " ".join(payload["algebraic_transport"])

        self.assertTrue(payload["algebraic_transport_closed"])
        self.assertIn("T_minus^{AB}=rho_minus u_minus^A u_minus^B", setup)
        self.assertIn("L^T eta L=eta", setup)
        self.assertIn("K_plus^{AB}=rho_minus u_{-to+}^A u_{-to+}^B", transport)
        self.assertIn("K_minus^{AB}=rho_plus u_{+to-}^A u_{+to-}^B", transport)

    def test_optical_contractions_have_no_raw_scale_ratio_amplitude(self) -> None:
        report = render_markdown(build_payload())

        self.assertIn("K_plus_kk=rho_minus (k_plus.u_{-to+})^2", report)
        self.assertIn("K_minus_kk=rho_plus (k_minus.u_{+to-})^2", report)
        self.assertNotIn("a_minus/a_plus", report)
        self.assertNotIn("a-/a+", report)
        self.assertNotIn("raw_flrw_scale_ratio", report)

    def test_algebraic_transport_is_separate_from_divergence_closure(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["divergence_blockers"])

        self.assertTrue(payload["algebraic_transport_closed"])
        self.assertFalse(payload["divergence_closure_closed"])
        self.assertIn("R_plus^mu", blockers)
        self.assertIn("R_minus^mu", blockers)
        self.assertIn("does not imply covariant divergence closure", blockers)

    def test_prediction_remains_blocked(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("prediction claims remain blocked", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
