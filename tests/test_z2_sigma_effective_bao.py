import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from src.janus_lab.z2_sigma_effective_bao import load_effective_scale_free_primitive_inputs


def _manifest(source_path: Path, source_hash: str) -> dict:
    z = (np.geomspace(1.0, 1.0e5, 128) - 1.0).tolist()
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_primitives",
        "manifest_kind": "effective_scale_free_primitive_inputs",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "source_effective_closure_path": str(source_path),
        "source_effective_closure_sha256": source_hash,
        "z_grid": z,
        "E_Z2Sigma": [float(np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)) for zz in z],
        "c_s_over_c_Z2Sigma": [1.0 / np.sqrt(3.0) for _ in z],
        "Gamma_drag_over_H0_Z2Sigma": [1.0e5 / (1.0 + zz) for zz in z],
        "omega_k_Z2Sigma": 0.0,
        "z_max": z[-1],
        "z_d_bracket": [100.0, 2000.0],
        "primitive_provenance": {
            "E_Z2Sigma": "effective_background_equation",
            "c_s_over_c_Z2Sigma": "effective_plasma_equation",
            "Gamma_drag_over_H0_Z2Sigma": "effective_drag_equation",
            "omega_k_Z2Sigma": "effective_curvature_convention",
        },
    }


class Z2SigmaEffectiveBAOTest(unittest.TestCase):
    def test_loads_valid_effective_primitives(self):
        with tempfile.TemporaryDirectory() as tmp:
            closure = Path(tmp) / "effective_closure_inputs.json"
            closure.write_text("{}", encoding="utf-8")
            path = Path(tmp) / "effective_bao.json"
            path.write_text(
                json.dumps(_manifest(closure, hashlib.sha256(closure.read_bytes()).hexdigest())),
                encoding="utf-8",
            )
            loaded = load_effective_scale_free_primitive_inputs(path)
        self.assertEqual(loaded.z_grid.ndim, 1)
        self.assertGreater(loaded.z_max, loaded.z_grid[0])

    def test_rejects_no_fit_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            closure = Path(tmp) / "effective_closure_inputs.json"
            closure.write_text("{}", encoding="utf-8")
            path = Path(tmp) / "effective_bao.json"
            manifest = _manifest(closure, hashlib.sha256(closure.read_bytes()).hexdigest())
            manifest["full_no_fit_prediction_ready"] = True
            path.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "false-required"):
                load_effective_scale_free_primitive_inputs(path)


if __name__ == "__main__":
    unittest.main()
