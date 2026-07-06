import json
import tempfile
import unittest
from pathlib import Path

from tests.test_p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f_script import _bulk_f
from scripts.run_p0_eft_janus_z2_sigma_dynamic_shell_chain import build_payload


def _coeff() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "a0": 1.0,
        "a1": 0.0,
        "a2": 0.0,
        "a3": 0.0,
    }


class JanusZ2SigmaDynamicShellChainScriptTest(unittest.TestCase):
    def test_missing_inputs_report_first_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(base=Path(tmp) / "sigma", cover=Path(tmp) / "cover")
        self.assertFalse(payload["chain_passed"])
        self.assertEqual(
            payload["first_blocker"],
            "active_unit_intrinsic_metric_q_ab_inputs",
        )

    def test_chain_writes_sigma_alpha_h_when_all_inputs_exist(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "sigma"
            cover = Path(tmp) / "cover"
            base.mkdir()
            cover.mkdir()
            (base / "rsigma_radius_solution.json").write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "observational_fit_used": False,
                        "a_grid": [0.5, 1.0, 1.5],
                        "R_Sigma_of_a": [2.0, 4.0, 6.0],
                        "z2_orientation_sign": -1.0,
                        "rsigma_solution_provenance": "active minimal radius solution",
                    }
                ),
                encoding="utf-8",
            )
            bulk = _bulk_f()
            bulk["a_grid"] = [0.5, 1.0, 1.5]
            for key in ["f_plus_of_R", "f_minus_of_R", "df_plus_dR", "df_minus_dR"]:
                bulk[key] = [bulk[key][0], bulk[key][1], bulk[key][1]]
            (base / "static_areal_bulk_f_pm_inputs.json").write_text(
                json.dumps(bulk),
                encoding="utf-8",
            )
            (base / "surface_hk_active_density_coefficients.json").write_text(
                json.dumps(_coeff()),
                encoding="utf-8",
            )

            payload = build_payload(base=base, cover=cover)
            alpha_h = json.loads((cover / "sigma_alpha_h_inputs.json").read_text(encoding="utf-8"))

        self.assertTrue(payload["chain_passed"])
        self.assertEqual(payload["first_blocker"], "none")
        self.assertEqual(alpha_h["parameter_grid"], [0.5, 1.0, 1.5])
        self.assertEqual(len(payload["steps"]), 8)


if __name__ == "__main__":
    unittest.main()
