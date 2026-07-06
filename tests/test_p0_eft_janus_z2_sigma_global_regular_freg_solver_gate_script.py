import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_solver_gate import (
    build_payload,
)


def _manifest() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_components",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": [1.0, 2.0, 3.0],
        "normal_frame_holonomy_defect": [4.0, 0.0, 4.0],
        "collar_endpoint_mismatch": [0.0, 0.0, 0.0],
        "junction_bianchi_defect": [0.0, 0.0, 0.0],
        "component_provenance": {
            "normal_frame_holonomy_defect": "active_collar_connection",
            "collar_endpoint_mismatch": "active_deck_pullback",
            "junction_bianchi_defect": "active_surface_bianchi",
        },
    }


class JanusZ2SigmaGlobalRegularFregSolverGateTest(unittest.TestCase):
    def test_missing_manifest_blocks(self):
        payload = build_payload(input_path=Path("__missing_freg__.json"))
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["F_reg_value_ready"])
        self.assertEqual(payload["primary_blocker"], "global_regular_freg_components_json")

    def test_unique_regular_root_passes_solver_gate_without_no_fit_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "global_regular_freg_components.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")
            payload = build_payload(input_path=path)
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["R_Sigma_over_ell_collar_selected"])
        self.assertEqual(payload["regularity_roots"], [2.0])
        self.assertFalse(payload["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
