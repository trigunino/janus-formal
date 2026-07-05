import json
import hashlib
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_bao_official_chi2_gate import build_payload
from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_bao_inputs,
    load_active_z2sigma_scale_free_bao_inputs,
    write_active_z2sigma_bao_manifest,
    write_active_z2sigma_scale_free_bao_manifest,
)


def _input_provenance() -> dict[str, str]:
    return {
        "H_Z2Sigma": "active_effective_fluid_background_component_manifest",
        "c_s_Z2Sigma": "active_early_plasma_component_manifest",
        "z_d_Z2Sigma": "active_Gamma_drag_equals_H_solver",
        "r_d_Z2Sigma": "active_sound_ruler_integrator",
    }


def _scale_free_input_provenance() -> dict[str, str]:
    return {
        "E_Z2Sigma": "active_dimensionless_background_component_manifest",
        "c_s_over_c_Z2Sigma": "active_early_plasma_sound_speed_over_c_manifest",
        "z_d_Z2Sigma": "active_scale_free_drag_solver",
        "rhat_d_Z2Sigma": "active_dimensionless_sound_ruler_integrator",
    }


def _source_hash() -> str:
    return "a" * 64


def _source_path(path: Path | None = None) -> str:
    return str(path or Path("outputs/active_z2_sigma/bao_component_inputs.json"))


class P0EFTJanusZ2SigmaBAOOfficialChi2GateTests(unittest.TestCase):
    def test_gate_blocks_without_active_manifest(self):
        payload = build_payload(Path("does/not/exist.json"))

        self.assertFalse(payload["active_manifest_available"])
        self.assertFalse(payload["official_bao_evaluation"])
        self.assertFalse(payload["bao_chi2_evaluated"])

    def test_loader_rejects_forbidden_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            path.write_text(json.dumps({"active_core": "Z2_tunnel_Sigma", "source": "demo"}), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_active_z2sigma_bao_inputs(path)

    def test_loader_requires_input_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            z = np.asarray([0.0, 1.0, 2.0])
            payload = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_rd_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "z_grid": z.tolist(),
                "H_Z2Sigma_km_s_Mpc": [70.0, 100.0, 120.0],
                "omega_k_Z2Sigma": 0.0,
                "c_s_Z2Sigma_km_s": [100000.0, 100000.0, 100000.0],
                "z_d_Z2Sigma": 1.0,
                "z_max": 2.0,
                "source_component_manifest_path": _source_path(),
                "source_component_manifest_sha256": _source_hash(),
            }
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_active_z2sigma_bao_inputs(path)

    def test_loader_requires_source_component_manifest_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            z = np.asarray([0.0, 1.0, 2.0])
            payload = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_rd_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "z_grid": z.tolist(),
                "H_Z2Sigma_km_s_Mpc": [70.0, 100.0, 120.0],
                "omega_k_Z2Sigma": 0.0,
                "c_s_Z2Sigma_km_s": [100000.0, 100000.0, 100000.0],
                "z_d_Z2Sigma": 1.0,
                "z_max": 2.0,
                "input_provenance": _input_provenance(),
                "source_component_manifest_path": _source_path(),
            }
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_active_z2sigma_bao_inputs(path)

    def test_gate_computes_when_active_manifest_is_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bao_inputs.json"
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            h = lambda zz: 70.0 * np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)
            cs = lambda zz: np.full_like(zz, 299792.458 / np.sqrt(3.0))
            source_path = Path(tmp) / "bao_component_inputs.json"
            source_path.write_text('{"active_core":"Z2_tunnel_Sigma"}', encoding="utf-8")
            write_active_z2sigma_bao_manifest(
                path,
                z,
                h,
                cs,
                1060.0,
                1.0e5 - 1.0,
                input_provenance=_input_provenance(),
                source_component_manifest_path=_source_path(source_path),
                source_component_manifest_sha256="a" * 64,
            )

            result = build_payload(path)

        self.assertTrue(result["active_manifest_available"])
        self.assertTrue(result["official_bao_evaluation"])
        self.assertTrue(result["bao_chi2_evaluated"])
        self.assertTrue(result["source_component_manifest_available"])
        self.assertFalse(result["source_hash_matches_manifest"])
        self.assertFalse(result["bao_official_chi2_gate_passed"])
        self.assertEqual(result["data_points"], 13)
        self.assertEqual(len(result["prediction_vector"]), 13)
        self.assertGreater(result["chi2_DESI_DR2_BAO"], 0.0)

    def test_gate_verifies_matching_source_manifest_hash_when_available(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "bao_inputs.json"
            source_path = tmpdir / "bao_component_inputs.json"
            source_path.write_text('{"active_core":"Z2_tunnel_Sigma"}', encoding="utf-8")
            source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            h = lambda zz: 70.0 * np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)
            cs = lambda zz: np.full_like(zz, 299792.458 / np.sqrt(3.0))
            write_active_z2sigma_bao_manifest(
                input_path,
                z,
                h,
                cs,
                1060.0,
                1.0e5 - 1.0,
                input_provenance=_input_provenance(),
                source_component_manifest_path=str(source_path),
                source_component_manifest_sha256=source_hash,
            )

            result = build_payload(input_path)

        self.assertTrue(result["source_component_manifest_available"])
        self.assertTrue(result["source_hash_matches_manifest"])
        self.assertTrue(result["bao_official_chi2_gate_passed"])

    def test_scale_free_manifest_loader_matches_dimensional_rd_hat(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "bao_scale_free_inputs.json"
            source_path = tmpdir / "bao_component_inputs.json"
            source_path.write_text('{"active_core":"Z2_tunnel_Sigma"}', encoding="utf-8")
            source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            e = lambda zz: np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)
            cs_over_c = lambda zz: np.full_like(zz, 1.0 / np.sqrt(3.0))
            write_active_z2sigma_scale_free_bao_manifest(
                input_path,
                z,
                e,
                cs_over_c,
                1060.0,
                1.0e5 - 1.0,
                input_provenance=_scale_free_input_provenance(),
                source_component_manifest_path=str(source_path),
                source_component_manifest_sha256=source_hash,
            )

            loaded = load_active_z2sigma_scale_free_bao_inputs(input_path)

        self.assertGreater(loaded.rd_hat(), 0.0)
        np.testing.assert_allclose(loaded.e_z2sigma(np.asarray([0.0])), [1.0])

    def test_scale_free_manifest_rejects_stale_rhat(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "bao_scale_free_inputs.json"
            source_path = tmpdir / "bao_component_inputs.json"
            source_path.write_text('{"active_core":"Z2_tunnel_Sigma"}', encoding="utf-8")
            source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            z = np.geomspace(1.0, 1.0e5, 256) - 1.0
            e = lambda zz: np.sqrt(0.3 * (1.0 + zz) ** 3 + 0.7)
            cs_over_c = lambda zz: np.full_like(zz, 1.0 / np.sqrt(3.0))
            write_active_z2sigma_scale_free_bao_manifest(
                input_path,
                z,
                e,
                cs_over_c,
                1060.0,
                1.0e5 - 1.0,
                input_provenance=_scale_free_input_provenance(),
                source_component_manifest_path=str(source_path),
                source_component_manifest_sha256=source_hash,
            )
            payload = json.loads(input_path.read_text(encoding="utf-8"))
            payload["rhat_d_Z2Sigma"] *= 1.01
            input_path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_scale_free_bao_inputs(input_path)

    def test_scale_free_manifest_rejects_forbidden_kind_and_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            path.write_text(
                json.dumps({
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "manifest_kind": "wrong",
                }),
                encoding="utf-8",
            )
            with self.assertRaises(ValueError):
                load_active_z2sigma_scale_free_bao_inputs(path)


if __name__ == "__main__":
    unittest.main()
