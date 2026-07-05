import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_certificate_from_radial_terms_gate import (
    build_payload,
)


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


def _input_payload(*, counterterm=None) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "E_CartanGHY": [1.0, 2.0],
        "E_HolstNiehYan": [0.5, 0.25],
        "E_matterFlux": [-0.25, -0.25],
        "E_counterterm": counterterm if counterterm is not None else [-1.25, -2.0],
        "term_provenance": {
            "E_CartanGHY": "active Cartan-GHY radial block",
            "E_HolstNiehYan": "active Holst Nieh-Yan radial block",
            "E_matterFlux": "active matter flux radial block",
            "E_counterterm": "active counterterm radial block",
        },
        "certificate_payload": _certificate_payload(),
    }


class RSigmaCertificateFromRadialTermsGateTests(unittest.TestCase):
    def test_zero_residual_terms_write_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "terms.json"
            output = root / "rsigma.json"
            source.write_text(json.dumps(_input_payload()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            cert = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(payload["R_Sigma_solution_residual_max_abs"], 0.0)
        self.assertIn("E_RSigma", cert["effective_RSigma_equation"])

    def test_nonzero_residual_blocks_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "terms.json"
            output = root / "rsigma.json"
            source.write_text(
                json.dumps(_input_payload(counterterm=[0.0, 0.0])),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=output)

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(output.exists())
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertIn("residual exceeds tolerance", payload["validation_error"])

    def test_forbidden_term_provenance_blocks_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "terms.json"
            output = root / "rsigma.json"
            payload = _input_payload()
            payload["term_provenance"]["E_CartanGHY"] = "Planck LCDM fit"
            source.write_text(json.dumps(payload), encoding="utf-8")

            result = build_payload(input_path=source, output_path=output)

        self.assertFalse(result["gate_passed"])
        self.assertIn("Forbidden provenance", result["validation_error"])


if __name__ == "__main__":
    unittest.main()
