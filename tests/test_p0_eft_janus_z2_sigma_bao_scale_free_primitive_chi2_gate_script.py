import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_primitive_inputs,
    write_active_z2sigma_scale_free_primitive_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_chi2_gate import (
    build_payload,
)


def _primitive_manifest(path: Path) -> None:
    z = np.geomspace(1.0, 1.0e5, 256) - 1.0
    e = np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    gamma_over_h0 = e * ((z + 1.0) / 1001.0)
    write_active_z2sigma_scale_free_primitive_manifest(
        path,
        z,
        lambda zz: np.interp(zz, z, e),
        lambda zz: np.full_like(zz, 1.0 / np.sqrt(3.0)),
        lambda zz: np.interp(zz, z, gamma_over_h0),
        0.0,
        float(z[-1]),
        primitive_provenance={
            "E_Z2Sigma": "active_Z2Sigma_dimensionless_background_derivation",
            "c_s_over_c_Z2Sigma": "active_Z2Sigma_photon_baryon_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": "active_Z2Sigma_Thomson_drag_over_H0_derivation",
            "omega_k_Z2Sigma": "active_Z2Sigma_projective_curvature_derivation",
        },
    )


class P0EFTJanusZ2SigmaBAOScaleFreePrimitiveChi2GateTests(unittest.TestCase):
    def test_missing_primitive_manifest_blocks_gate(self):
        payload = build_payload(Path("missing/primitives.json"), Path("missing/out.json"))

        self.assertFalse(payload["primitive_input_manifest_available"])
        self.assertFalse(payload["scale_free_bao_evaluation"])
        self.assertFalse(payload["gate_passed"])

    def test_primitive_manifest_writes_scale_free_inputs_and_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            primitive_path = tmpdir / "bao_scale_free_primitive_inputs.json"
            scale_free_path = tmpdir / "bao_scale_free_inputs.json"
            _primitive_manifest(primitive_path)

            payload = build_payload(primitive_path, scale_free_path)
            output = json.loads(scale_free_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["primitive_input_manifest_available"])
        self.assertTrue(payload["scale_free_bao_input_manifest_written"])
        self.assertTrue(payload["active_scale_free_bao_input_valid"])
        self.assertTrue(payload["scale_free_bao_evaluation"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["Gamma_drag_over_H0_Z2Sigma_available"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(len(payload["prediction_vector"]), 13)
        self.assertEqual(len(payload["residual_vector"]), 13)
        self.assertGreater(payload["chi2_DESI_DR2_BAO"], 0.0)
        self.assertEqual(output["manifest_kind"], "scale_free_bao_inputs")
        self.assertAlmostEqual(output["z_d_Z2Sigma"], 1000.0, delta=0.1)
        self.assertEqual(
            output["source_component_manifest_path"],
            str(primitive_path),
        )

    def test_primitive_writer_loader_rejects_forbidden_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad_primitives.json"
            _primitive_manifest(path)
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["primitive_provenance"]["E_Z2Sigma"] = "planck_lcdm_prior"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_scale_free_primitive_inputs(path)


if __name__ == "__main__":
    unittest.main()
