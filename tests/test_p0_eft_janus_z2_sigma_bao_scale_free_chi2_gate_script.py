import hashlib
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import write_active_z2sigma_scale_free_bao_manifest
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_chi2_gate import build_payload


def _input_provenance() -> dict[str, str]:
    return {
        "E_Z2Sigma": "active_dimensionless_background_component_manifest",
        "c_s_over_c_Z2Sigma": "active_early_plasma_sound_speed_over_c_manifest",
        "z_d_Z2Sigma": "active_scale_free_drag_solver",
        "rhat_d_Z2Sigma": "active_dimensionless_sound_ruler_integrator",
    }


class P0EFTJanusZ2SigmaBAOScaleFreeChi2GateTests(unittest.TestCase):
    def test_gate_blocks_without_scale_free_manifest(self):
        payload = build_payload(Path("does/not/exist.json"))

        self.assertFalse(payload["active_manifest_available"])
        self.assertFalse(payload["scale_free_bao_evaluation"])
        self.assertFalse(payload["bao_chi2_evaluated"])

    def test_gate_computes_with_strict_scale_free_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "bao_scale_free_inputs.json"
            source_path = tmpdir / "bao_component_inputs.json"
            source_path.write_text('{"active_core":"Z2_tunnel_Sigma"}', encoding="utf-8")
            source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            e = lambda zz: np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)
            cs_over_c = lambda zz: np.full_like(zz, 1.0 / np.sqrt(3.0))
            gamma_over_h0 = lambda zz: 10.0 + 0.0 * zz
            write_active_z2sigma_scale_free_bao_manifest(
                input_path,
                z,
                e,
                cs_over_c,
                1060.0,
                1.0e5 - 1.0,
                gamma_drag_over_h0_z2sigma=gamma_over_h0,
                input_provenance=_input_provenance(),
                source_component_manifest_path=str(source_path),
                source_component_manifest_sha256=source_hash,
            )

            payload = build_payload(input_path)

        self.assertTrue(payload["active_manifest_available"])
        self.assertTrue(payload["scale_free_bao_evaluation"])
        self.assertFalse(payload["official_dimensional_bao_gate_unblocked"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["source_hash_matches_manifest"])
        self.assertTrue(payload["bao_scale_free_chi2_gate_passed"])
        self.assertEqual(payload["data_points"], 13)
        self.assertEqual(len(payload["prediction_vector"]), 13)
        self.assertEqual(payload["prediction_vector_length"], 13)
        self.assertEqual(payload["residual_vector_length"], 13)
        self.assertEqual(len(payload["E_Z2Sigma_sample"]), 3)
        self.assertEqual(len(payload["c_s_over_c_Z2Sigma_sample"]), 3)
        self.assertTrue(payload["Gamma_drag_over_H0_Z2Sigma_available"])
        self.assertEqual(len(payload["Gamma_drag_over_H0_Z2Sigma_sample"]), 3)
        self.assertGreater(payload["chi2_DESI_DR2_BAO"], 0.0)


if __name__ == "__main__":
    unittest.main()
