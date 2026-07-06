import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate import (
    build_payload,
)


class JanusZ2SigmaEffectiveBAOScaleFreeChi2GateTest(unittest.TestCase):
    def test_missing_manifest_blocks_gate(self):
        payload = build_payload(Path("__missing_effective_bao__.json"))
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["effective_bao_chi2_evaluated"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_valid_effective_primitives_evaluate_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            closure = tmpdir / "effective_closure_inputs.json"
            closure.write_text('{"source":"effective_initial_data"}', encoding="utf-8")
            closure_hash = hashlib.sha256(closure.read_bytes()).hexdigest()
            path = tmpdir / "effective_bao_scale_free_primitive_inputs.json"
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "effective_primitives",
                        "manifest_kind": "effective_scale_free_primitive_inputs",
                        "compressed_planck_lcdm_used": False,
                        "archived_z4_reuse_used": False,
                        "observational_fit_used": False,
                        "full_no_fit_prediction_ready": False,
                        "source_effective_closure_path": str(closure),
                        "source_effective_closure_sha256": closure_hash,
                        "z_grid": z.tolist(),
                        "E_Z2Sigma": np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7).tolist(),
                        "c_s_over_c_Z2Sigma": np.full_like(z, 1.0 / np.sqrt(3.0)).tolist(),
                        "Gamma_drag_over_H0_Z2Sigma": (1.0e5 / (1.0 + z)).tolist(),
                        "omega_k_Z2Sigma": 0.0,
                        "z_max": float(z[-1]),
                        "z_d_bracket": [100.0, 2000.0],
                        "primitive_provenance": {
                            "E_Z2Sigma": "effective_background_equation",
                            "c_s_over_c_Z2Sigma": "effective_plasma_equation",
                            "Gamma_drag_over_H0_Z2Sigma": "effective_drag_equation",
                            "omega_k_Z2Sigma": "effective_curvature_convention",
                        },
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["effective_bao_chi2_evaluated"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(payload["prediction_vector_length"], 13)
        self.assertEqual(payload["residual_vector_length"], 13)
        self.assertGreater(payload["chi2_DESI_DR2_BAO_effective"], 0.0)


if __name__ == "__main__":
    unittest.main()
