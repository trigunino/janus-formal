import unittest

from src.janus_lab.z2_cover_master_action import derive_projected_equations


def _payload() -> dict:
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "explicit_master_action_projection",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "kappa_symbol": "kappa_J",
        "B_minus_to_plus": "B_minus_to_plus",
        "B_plus_to_minus": "B_plus_to_minus",
        "Sigma_plus_boundary_source": "J_Sigma_plus",
        "Sigma_minus_boundary_source": "J_Sigma_minus",
        "self_sector_orientation_sign": 1,
        "cross_sector_orientation_sign": -1,
    }


class Z2CoverMasterActionTest(unittest.TestCase):
    def test_derives_projected_equations_with_negative_cross_sign(self):
        out = derive_projected_equations(_payload())
        self.assertTrue(out["projected_equations_ready"])
        self.assertIn("- B_minus_to_plus", out["projected_equations"]["E_plus"])
        self.assertIn("- B_plus_to_minus", out["projected_equations"]["E_minus"])
        self.assertFalse(out["negative_thermodynamic_density_postulated"])
        self.assertFalse(out["rho_eff_shortcut_used"])

    def test_rejects_rho_eff_shortcut(self):
        payload = _payload()
        payload["rho_eff_shortcut_used"] = True
        with self.assertRaisesRegex(ValueError, "rho_eff_shortcut_used"):
            derive_projected_equations(payload)

    def test_rejects_fit_symbols(self):
        payload = _payload()
        payload["B_minus_to_plus"] = "fit_B"
        with self.assertRaisesRegex(ValueError, "forbidden"):
            derive_projected_equations(payload)


if __name__ == "__main__":
    unittest.main()
