import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_rsigma_radius_solution_from_isotropic_balance import (
    build_payload,
)


def _term(name: str, values: list[float]) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "term_name": name,
        "a_grid": [0.5, 1.0],
        "term_values": values,
        "term_provenance": f"active {name} radial block",
    }


def _q() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "unit_intrinsic_metric_q_ab": [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
        "kappa_Z2Sigma": 2.0,
    }


def _frame() -> dict:
    return {"active_core": "Z2_tunnel_Sigma", "source": "active_derived", "z2_orientation_sign": 1.0}


class RSigmaRadiusSolutionFromIsotropicBalanceScriptTest(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                term_paths={
                    "E_HolstNiehYan": Path(tmp) / "h.json",
                    "E_matterFlux": Path(tmp) / "m.json",
                    "E_counterterm": Path(tmp) / "c.json",
                },
                q_input_path=Path(tmp) / "q.json",
                frame_input_path=Path(tmp) / "f.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "minimal_rsigma_balance_inputs_missing")

    def test_writes_minimal_radius_solution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = {
                "E_HolstNiehYan": root / "h.json",
                "E_matterFlux": root / "m.json",
                "E_counterterm": root / "c.json",
            }
            paths["E_HolstNiehYan"].write_text(json.dumps(_term("E_HolstNiehYan", [-1.0, -2.0])), encoding="utf-8")
            paths["E_matterFlux"].write_text(json.dumps(_term("E_matterFlux", [-2.0, -3.0])), encoding="utf-8")
            paths["E_counterterm"].write_text(json.dumps(_term("E_counterterm", [-3.0, -4.0])), encoding="utf-8")
            q = root / "q.json"
            frame = root / "frame.json"
            out = root / "radius.json"
            q.write_text(json.dumps(_q()), encoding="utf-8")
            frame.write_text(json.dumps(_frame()), encoding="utf-8")

            payload = build_payload(
                term_paths=paths,
                q_input_path=q,
                frame_input_path=frame,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_Sigma_of_a"], [2.0, 3.0])
        self.assertEqual(written["z2_orientation_sign"], 1.0)


if __name__ == "__main__":
    unittest.main()
