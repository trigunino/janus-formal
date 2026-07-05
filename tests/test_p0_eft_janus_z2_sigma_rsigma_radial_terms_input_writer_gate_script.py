import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_radial_terms_input_writer_gate import (
    build_payload,
)


def _term(name: str, values: list[float], provenance: str | None = None) -> dict:
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
        "term_provenance": provenance or f"active {name} derivation",
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


class RSigmaRadialTermsInputWriterGateTests(unittest.TestCase):
    def test_four_term_manifests_write_combined_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = {
                "E_CartanGHY": root / "cartan.json",
                "E_HolstNiehYan": root / "holst.json",
                "E_matterFlux": root / "matter.json",
                "E_counterterm": root / "counterterm.json",
            }
            paths["E_CartanGHY"].write_text(json.dumps(_term("E_CartanGHY", [1.0, 2.0])), encoding="utf-8")
            paths["E_HolstNiehYan"].write_text(json.dumps(_term("E_HolstNiehYan", [0.5, 0.25])), encoding="utf-8")
            paths["E_matterFlux"].write_text(json.dumps(_term("E_matterFlux", [-0.25, -0.25])), encoding="utf-8")
            paths["E_counterterm"].write_text(json.dumps(_term("E_counterterm", [-1.25, -2.0])), encoding="utf-8")
            certificate = root / "certificate_payload.json"
            output = root / "terms_input.json"
            certificate.write_text(json.dumps(_certificate_payload()), encoding="utf-8")

            payload = build_payload(
                term_paths=paths,
                certificate_payload_path=certificate,
                output_path=output,
            )
            merged = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(merged["E_counterterm"], [-1.25, -2.0])
        self.assertIn("E_CartanGHY", merged["term_provenance"])

    def test_missing_or_forbidden_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = {
                "E_CartanGHY": root / "cartan.json",
                "E_HolstNiehYan": root / "holst.json",
                "E_matterFlux": root / "matter.json",
                "E_counterterm": root / "counterterm.json",
            }
            paths["E_CartanGHY"].write_text(
                json.dumps(_term("E_CartanGHY", [1.0, 2.0], provenance="Planck fit")),
                encoding="utf-8",
            )
            for name in ["E_HolstNiehYan", "E_matterFlux", "E_counterterm"]:
                paths[name].write_text(json.dumps(_term(name, [0.0, 0.0])), encoding="utf-8")
            certificate = root / "certificate_payload.json"
            certificate.write_text(json.dumps(_certificate_payload()), encoding="utf-8")

            payload = build_payload(term_paths=paths, certificate_payload_path=certificate)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
