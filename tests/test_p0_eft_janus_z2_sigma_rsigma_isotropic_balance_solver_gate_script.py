import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_isotropic_balance_solver_gate import (
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
        "unit_intrinsic_metric_q_ab_provenance": "active projective throat unit metric",
        "radial_offsets": [-0.1, 0.0, 0.1],
        "ambient_coordinate_offsets": [[0.0, 0.0, 0.0, 0.0]],
        "intrinsic_coordinate_offsets": [[0.0, 0.0, 0.0]],
        "kappa_Z2Sigma": 2.0,
    }


def _certificate_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "R_Sigma_solution_certificate_type": "conditional_closed_frontier_solution",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [1.0, 1.0],
        "X_plus_of_a": [[[1.0]], [[1.0]]],
        "X_minus_of_a": [[[-1.0]], [[-1.0]]],
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
        "rsigma_solution_provenance": "active isotropic balance certificate",
    }


class RSigmaIsotropicBalanceSolverGateTests(unittest.TestCase):
    def test_solves_radius_and_writes_certificate_and_cartan_term(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = {
                "E_HolstNiehYan": root / "holst.json",
                "E_matterFlux": root / "matter.json",
                "E_counterterm": root / "counter.json",
            }
            paths["E_HolstNiehYan"].write_text(json.dumps(_term("E_HolstNiehYan", [-1.0, -2.0])), encoding="utf-8")
            paths["E_matterFlux"].write_text(json.dumps(_term("E_matterFlux", [-2.0, -3.0])), encoding="utf-8")
            paths["E_counterterm"].write_text(json.dumps(_term("E_counterterm", [-3.0, -4.0])), encoding="utf-8")
            q_path = root / "q.json"
            cert_payload = root / "cert_payload.json"
            cert_out = root / "cert.json"
            cartan_out = root / "cartan.json"
            q_path.write_text(json.dumps(_q()), encoding="utf-8")
            cert_payload.write_text(json.dumps(_certificate_payload()), encoding="utf-8")

            payload = build_payload(
                term_paths=paths,
                q_input_path=q_path,
                certificate_payload_path=cert_payload,
                certificate_output_path=cert_out,
                cartan_output_path=cartan_out,
            )
            cert = json.loads(cert_out.read_text(encoding="utf-8"))
            cartan = json.loads(cartan_out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(cert["R_Sigma_of_a"], [2.0, 3.0])
        self.assertEqual(cartan["term_values"], [6.0, 9.0])
        self.assertEqual(payload["R_Sigma_solution_residual_max_abs"], 0.0)

    def test_nonpositive_radius_solution_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = {
                "E_HolstNiehYan": root / "holst.json",
                "E_matterFlux": root / "matter.json",
                "E_counterterm": root / "counter.json",
            }
            paths["E_HolstNiehYan"].write_text(json.dumps(_term("E_HolstNiehYan", [1.0, 1.0])), encoding="utf-8")
            paths["E_matterFlux"].write_text(json.dumps(_term("E_matterFlux", [0.0, 0.0])), encoding="utf-8")
            paths["E_counterterm"].write_text(json.dumps(_term("E_counterterm", [0.0, 0.0])), encoding="utf-8")
            q_path = root / "q.json"
            cert_payload = root / "cert_payload.json"
            q_path.write_text(json.dumps(_q()), encoding="utf-8")
            cert_payload.write_text(json.dumps(_certificate_payload()), encoding="utf-8")

            payload = build_payload(term_paths=paths, q_input_path=q_path, certificate_payload_path=cert_payload)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("positive R_Sigma", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
