import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_rsigma_certificate import (
    load_active_z2sigma_rsigma_solution_certificate,
    write_active_z2sigma_rsigma_solution_certificate,
)


def _certificate() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "effective_RSigma_equation": (
            "E_RSigma(a) := E_CartanGHY(a) + E_HolstNiehYan(a) "
            "+ E_matterFlux(a) + E_counterterm(a) = 0"
        ),
        "R_Sigma_solution_certificate_type": "conditional_closed_frontier_solution",
        "R_Sigma_solution_residual_max_abs": 0.0,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [1.0, 1.1],
        "X_plus_of_a": [[[1.0]], [[1.1]]],
        "X_minus_of_a": [[[-1.0]], [[-1.1]]],
        "R_curv_Z2Sigma_Mpc": 3000.0,
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
        "rsigma_solution_provenance": "active conditional E_RSigma solution",
    }


class Z2SigmaRSigmaCertificateTests(unittest.TestCase):
    def test_valid_certificate_round_trips(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "rsigma.json"
            write_active_z2sigma_rsigma_solution_certificate(path, _certificate())

            payload = load_active_z2sigma_rsigma_solution_certificate(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertIn("E_RSigma", payload["effective_RSigma_equation"])

    def test_forbidden_planck_or_large_residual_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "rsigma.json"
            payload = _certificate()
            payload["compressed_planck_lcdm_background_used"] = True
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_rsigma_solution_certificate(path)

        payload = _certificate()
        payload["R_Sigma_solution_residual_max_abs"] = 1.0e-3
        with self.assertRaises(ValueError):
            write_active_z2sigma_rsigma_solution_certificate(Path("unused.json"), payload)


if __name__ == "__main__":
    unittest.main()
