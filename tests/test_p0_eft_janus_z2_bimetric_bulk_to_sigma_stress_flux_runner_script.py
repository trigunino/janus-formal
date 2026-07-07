import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_sigma_stress_flux_runner import (
    build_payload,
)


def _source():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [1.0, 2.0],
        "rho_plus_values": [2.0, 2.0],
        "p_plus_values": [0.0, 0.0],
        "rho_minus_values": [-1.0, -1.0],
        "p_minus_values": [0.0, 0.0],
        "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
        "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
        "u_plus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
        "u_minus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
        "tangent_vectors_values": [[[1.0, 0.0]], [[1.0, 0.0]]],
        "normal_plus_values": [[0.0, 1.0], [0.0, 1.0]],
        "normal_minus_values": [[0.0, -1.0], [0.0, -1.0]],
        "radial_variation_tangent_weights": [[1.0], [1.0]],
        "eps_Z2": -1.0,
    }


class BimetricBulkToSigmaStressFluxRunnerTests(unittest.TestCase):
    def test_blocks_without_active_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                input_path=root / "missing.json",
                stress_output_path=root / "stress.json",
                flux_output_path=root / "flux.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertIn("missing_bimetric_bulk_to_sigma_stress_flux_inputs", payload["blocked_by"])

    def test_transfers_bulk_stress_and_projects_flux(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "input.json"
            stress_path = root / "stress.json"
            flux_path = root / "flux.json"
            input_path.write_text(json.dumps(_source()), encoding="utf-8")
            payload = build_payload(
                input_path=input_path,
                stress_output_path=stress_path,
                flux_output_path=flux_path,
            )
            flux = json.loads(flux_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["bimetric_bulk_stress_transferred_to_sigma"])
        self.assertTrue(payload["sigma_stress_flux_projection_ready"])
        self.assertEqual(flux["selected_route"], "active_projection")
        self.assertEqual(flux["E_matterFlux_values"], [0.0, 0.0])


if __name__ == "__main__":
    unittest.main()
