import json
import tempfile
import unittest
from pathlib import Path

from tests.test_p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate_script import (
    _certificate,
)

from scripts.write_p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f import (
    build_payload,
)


def _kinematics() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "a_grid": [0.5, 1.0],
        "R_dot_of_a": [0.0, 0.0],
        "R_ddot_of_a": [0.0, 0.0],
        "kinematics_provenance": "active proper-time throat radius kinematics",
    }


def _bulk_f() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "a_grid": [0.5, 1.0],
        "f_plus_of_R": [4.0, 9.0],
        "f_minus_of_R": [1.0, 4.0],
        "df_plus_dR": [2.0, 4.0],
        "df_minus_dR": [1.0, 2.0],
        "epsilon_plus": 1.0,
        "epsilon_minus": -1.0,
        "bulk_f_provenance": "active static areal Janus/Z2 bulk chart",
    }


class DynamicShellInputsFromRSigmaAndBulkFScriptTest(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                certificate_path=Path(tmp) / "missing_cert.json",
                kinematics_path=Path(tmp) / "missing_kin.json",
                bulk_f_path=Path(tmp) / "missing_bulk.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["input_exists"]["rsigma_solution_certificate"])

    def test_writes_dynamic_shell_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "rsigma.json"
            kin = root / "kin.json"
            bulk = root / "bulk.json"
            out = root / "dynamic.json"
            cert.write_text(json.dumps(_certificate()), encoding="utf-8")
            kin.write_text(json.dumps(_kinematics()), encoding="utf-8")
            bulk.write_text(json.dumps(_bulk_f()), encoding="utf-8")

            payload = build_payload(
                certificate_path=cert,
                kinematics_path=kin,
                bulk_f_path=bulk,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_Sigma_of_a"], [1.0, 1.1])
        self.assertEqual(written["f_plus_of_R"], [4.0, 9.0])
        self.assertEqual(written["epsilon_minus"], -1.0)
        self.assertIn("bulk_f=", written["dynamic_shell_provenance"])

    def test_writes_from_minimal_radius_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            radius = root / "radius.json"
            kin = root / "kin.json"
            bulk = root / "bulk.json"
            out = root / "dynamic.json"
            radius.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "observational_fit_used": False,
                        "a_grid": [0.5, 1.0],
                        "R_Sigma_of_a": [2.0, 4.0],
                        "z2_orientation_sign": -1.0,
                        "rsigma_solution_provenance": "active minimal radius solution",
                    }
                ),
                encoding="utf-8",
            )
            kin.write_text(json.dumps(_kinematics()), encoding="utf-8")
            bulk.write_text(json.dumps(_bulk_f()), encoding="utf-8")

            payload = build_payload(
                certificate_path=radius,
                kinematics_path=kin,
                bulk_f_path=bulk,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_Sigma_of_a"], [2.0, 4.0])


if __name__ == "__main__":
    unittest.main()
