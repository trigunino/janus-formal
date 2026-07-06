import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_cover_bianchi_with_sigma_source import build_payload
from src.janus_lab.z2_cover_bianchi import derive_bianchi_balances
from src.janus_lab.z2_cover_master_action import derive_projected_equations


def _balance() -> dict:
    projected = derive_projected_equations(
        {
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
    )
    return derive_bianchi_balances(projected)


class JanusZ2CoverBianchiWithSigmaSourceScriptTest(unittest.TestCase):
    def test_blocks_without_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                Path(tmp) / "missing_balance.json",
                Path(tmp) / "missing_sigma.json",
                Path(tmp) / "out.json",
            )
        self.assertFalse(payload["gate_passed"])

    def test_writes_attached_balance(self):
        with tempfile.TemporaryDirectory() as tmp:
            balance_path = Path(tmp) / "balance.json"
            sigma_path = Path(tmp) / "sigma.json"
            output_path = Path(tmp) / "out.json"
            balance_path.write_text(json.dumps(_balance()), encoding="utf-8")
            sigma_path.write_text(
                json.dumps(
                    {
                        "active_core": "JanusZ2CoverMasterAction",
                        "sigma_source_ready": True,
                        "sigma_junction_derived": True,
                        "J_Sigma_plus_tau": [-1.0],
                        "J_Sigma_plus_s": [-2.0],
                        "J_Sigma_minus_tau": [1.0],
                        "J_Sigma_minus_s": [2.0],
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(balance_path, sigma_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["sigma_source_attached"])
        self.assertFalse(written["paired_bianchi_closed"])


if __name__ == "__main__":
    unittest.main()
