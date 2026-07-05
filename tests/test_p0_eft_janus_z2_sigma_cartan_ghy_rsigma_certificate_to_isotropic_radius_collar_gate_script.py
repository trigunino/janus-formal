import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_gate import (
    build_payload,
)


def _certificate() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "effective_RSigma_equation": "E_RSigma(a) = 0",
        "R_Sigma_solution_certificate_type": "active_no_fit_solution",
        "R_Sigma_solution_residual_max_abs": 0.0,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [2.0, 3.0],
        "X_plus_of_a": [[[1.0]], [[1.1]]],
        "X_minus_of_a": [[[-1.0]], [[-1.1]]],
        "R_curv_Z2Sigma_Mpc": 10.0,
        "k_Z2Sigma": 1,
        "H0_Z2Sigma_km_s_Mpc": 70.0,
        "tangent_frames_plus": [[[1.0]], [[1.0]]],
        "tangent_frames_minus": [[[-1.0]], [[-1.0]]],
        "unit_normals_plus": [[[1.0]], [[1.0]]],
        "unit_normals_minus": [[[-1.0]], [[-1.0]]],
        "christoffels_plus": [[[0.0]], [[0.0]]],
        "christoffels_minus": [[[0.0]], [[0.0]]],
        "spatial_inverse_metric": [[[1.0]], [[1.0]]],
        "z2_orientation_sign": 1.0,
        "rsigma_solution_provenance": "active R_Sigma variational certificate",
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
        "unit_intrinsic_metric_q_ab": [[1.0]],
        "unit_intrinsic_metric_q_ab_provenance": "active projective throat unit metric",
        "radial_offsets": [-0.1, 0.0, 0.1],
        "ambient_coordinate_offsets": [
            [0.0, 0.0],
            [-0.1, 0.0],
            [0.1, 0.0],
            [0.0, -0.1],
            [0.0, 0.1],
            [0.1, 0.1],
        ],
        "intrinsic_coordinate_offsets": [[-0.1], [0.0], [0.1]],
        "kappa_Z2Sigma": 2.0,
    }


class CertificateToIsotropicRadiusCollarGateTests(unittest.TestCase):
    def test_certificate_and_q_write_isotropic_radius_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "cert.json"
            q = root / "q.json"
            out = root / "radius.json"
            cert.write_text(json.dumps(_certificate()), encoding="utf-8")
            q.write_text(json.dumps(_q()), encoding="utf-8")

            payload = build_payload(certificate_path=cert, q_input_path=q, output_path=out)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["R_Sigma_of_a"], [2.0, 3.0])
        self.assertEqual(written["unit_intrinsic_metric_q_ab"], [[1.0]])
        self.assertFalse(written["observational_H0_fit_used"])

    def test_missing_q_or_forbidden_q_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "cert.json"
            cert.write_text(json.dumps(_certificate()), encoding="utf-8")

            payload = build_payload(certificate_path=cert, q_input_path=root / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["q_input_exists"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "cert.json"
            q = root / "q.json"
            cert.write_text(json.dumps(_certificate()), encoding="utf-8")
            bad = _q()
            bad["unit_intrinsic_metric_q_ab_provenance"] = "Planck LCDM fit"
            q.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(certificate_path=cert, q_input_path=q)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
