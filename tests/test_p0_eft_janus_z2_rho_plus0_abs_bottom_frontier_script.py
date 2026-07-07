import unittest

from scripts.run_p0_eft_janus_z2_rho_plus0_abs_bottom_frontier import build_payload


class RhoPlus0AbsBottomFrontierTests(unittest.TestCase):
    def test_live_frontier_keeps_state_and_radius_as_first_blockers(self):
        payload = build_payload()

        self.assertTrue(payload["rho_plus0_abs_formula_closed"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("N_occ_Z2Sigma", payload["first_physical_blockers"])
        self.assertIn("R_curv_Z2Sigma", payload["first_physical_blockers"])
        self.assertIn("use_LCDM_or_Planck_density", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
