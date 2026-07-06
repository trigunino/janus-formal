import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_cover_bianchi_balance import build_payload
from src.janus_lab.z2_cover_master_action import derive_projected_equations


def _projected() -> dict:
    return derive_projected_equations(
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


class JanusZ2CoverBianchiBalanceScriptTest(unittest.TestCase):
    def test_writes_bianchi_balance(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "projected.json"
            output_path = Path(tmp) / "bianchi.json"
            input_path.write_text(json.dumps(_projected()), encoding="utf-8")
            payload = build_payload(input_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["paired_bianchi_balance_ready"])
        self.assertFalse(written["paired_bianchi_closed"])


if __name__ == "__main__":
    unittest.main()
