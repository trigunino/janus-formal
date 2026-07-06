import unittest

from src.janus_lab.z2_cover_bianchi import (
    attach_sigma_source_to_bianchi_balance,
    derive_bianchi_balances,
)
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


class Z2CoverBianchiTest(unittest.TestCase):
    def test_extracts_sigma_balance_from_projected_equations(self):
        projected = derive_projected_equations(_payload())
        out = derive_bianchi_balances(projected)
        self.assertTrue(out["paired_bianchi_balance_ready"])
        self.assertFalse(out["paired_bianchi_closed"])
        self.assertIn("D_plus J_Sigma_plus", out["balances"]["plus"])
        self.assertEqual(
            out["primary_blocker"],
            "derive_cross_measure_transport_and_sigma_variation",
        )

    def test_rejects_unready_projection(self):
        projected = derive_projected_equations(_payload())
        projected["projected_equations_ready"] = False
        with self.assertRaisesRegex(ValueError, "projected equations"):
            derive_bianchi_balances(projected)

    def test_attaches_sigma_source_components(self):
        balance = derive_bianchi_balances(derive_projected_equations(_payload()))
        sigma = {
            "active_core": "JanusZ2CoverMasterAction",
            "sigma_source_ready": True,
            "sigma_junction_derived": True,
            "J_Sigma_plus_tau": [-1.0],
            "J_Sigma_plus_s": [-2.0],
            "J_Sigma_minus_tau": [1.0],
            "J_Sigma_minus_s": [2.0],
        }
        out = attach_sigma_source_to_bianchi_balance(balance, sigma)
        self.assertTrue(out["sigma_source_attached"])
        self.assertTrue(out["sigma_junction_derived"])
        self.assertFalse(out["paired_bianchi_closed"])
        self.assertEqual(out["sigma_source_components"]["plus_tau"], [-1.0])


if __name__ == "__main__":
    unittest.main()
