import json
import tempfile
import unittest
from pathlib import Path

from tests.test_p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate_script import (
    _certificate,
)

from scripts.write_p0_eft_janus_z2_sigma_radius_kinematics_from_rsigma import build_payload


class RadiusKinematicsFromRSigmaScriptTest(unittest.TestCase):
    def test_missing_certificate_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "kin.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "rsigma_solution_certificate_missing")

    def test_writes_finite_difference_kinematics(self):
        with tempfile.TemporaryDirectory() as tmp:
            cert_path = Path(tmp) / "rsigma.json"
            out_path = Path(tmp) / "kin.json"
            cert = _certificate()
            cert["a_grid"] = [0.5, 1.0, 1.5]
            cert["R_Sigma_of_a"] = [1.0, 2.0, 3.0]
            for key in [
                "X_plus_of_a",
                "X_minus_of_a",
                "tangent_frames_plus",
                "tangent_frames_minus",
                "unit_normals_plus",
                "unit_normals_minus",
                "christoffels_plus",
                "christoffels_minus",
                "spatial_inverse_metric",
            ]:
                cert[key] = [cert[key][0], cert[key][0], cert[key][0]]
            cert_path.write_text(json.dumps(cert), encoding="utf-8")

            payload = build_payload(input_path=cert_path, output_path=out_path)
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_dot_of_a"], [2.0, 2.0, 2.0])
        self.assertEqual(written["R_ddot_of_a"], [0.0, 0.0, 0.0])

    def test_writes_from_minimal_radius_solution(self):
        with tempfile.TemporaryDirectory() as tmp:
            in_path = Path(tmp) / "radius.json"
            out_path = Path(tmp) / "kin.json"
            in_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "observational_fit_used": False,
                        "a_grid": [0.5, 1.0, 1.5],
                        "R_Sigma_of_a": [1.0, 1.5, 2.0],
                        "z2_orientation_sign": -1.0,
                        "rsigma_solution_provenance": "active minimal radius solution",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=in_path, output_path=out_path)
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_dot_of_a"], [1.0, 1.0, 1.0])


if __name__ == "__main__":
    unittest.main()
