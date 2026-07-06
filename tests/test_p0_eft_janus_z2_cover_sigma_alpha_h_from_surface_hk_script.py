import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_cover_sigma_alpha_h_from_surface_hk import (
    build_payload,
)


def _coeff() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "a0": 1.0,
        "a1": 2.0,
        "a2": 3.0,
        "a3": 4.0,
    }


def _geom() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "parameter_grid": [1.0],
        "K_tau": [5.0],
        "K_s": [7.0],
        "sigma_orientation_plus": [1.0],
        "sigma_orientation_minus": [-1.0],
    }


class JanusZ2CoverSigmaAlphaHFromSurfaceHKScriptTest(unittest.TestCase):
    def test_blocks_without_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                Path(tmp) / "coeff.json",
                Path(tmp) / "geom.json",
                Path(tmp) / "out.json",
            )
        self.assertFalse(payload["gate_passed"])

    def test_writes_alpha_h_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            coeff_path = Path(tmp) / "coeff.json"
            geom_path = Path(tmp) / "geom.json"
            out_path = Path(tmp) / "out.json"
            coeff_path.write_text(json.dumps(_coeff()), encoding="utf-8")
            geom_path.write_text(json.dumps(_geom()), encoding="utf-8")
            payload = build_payload(coeff_path, geom_path, out_path)
            written = json.loads(out_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["alpha_h_tau"], [-744.5 - 98.0 * 5.0 + 200.0])
        self.assertEqual(written["alpha_h_s"], [744.5 - 98.0 * 7.0 - 392.0])

    def test_accepts_vector_coefficient_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            coeff = _coeff()
            for key in ["a0", "a1", "a2", "a3"]:
                coeff[f"{key}_values"] = [coeff.pop(key)]
            coeff_path = Path(tmp) / "coeff.json"
            geom_path = Path(tmp) / "geom.json"
            out_path = Path(tmp) / "out.json"
            coeff_path.write_text(json.dumps(coeff), encoding="utf-8")
            geom_path.write_text(json.dumps(_geom()), encoding="utf-8")
            payload = build_payload(coeff_path, geom_path, out_path)
        self.assertTrue(payload["gate_passed"])

    def test_rejects_background_forbidden_flags(self):
        with tempfile.TemporaryDirectory() as tmp:
            coeff = _coeff()
            coeff["compressed_planck_lcdm_background_used"] = True
            coeff_path = Path(tmp) / "coeff.json"
            geom_path = Path(tmp) / "geom.json"
            out_path = Path(tmp) / "out.json"
            coeff_path.write_text(json.dumps(coeff), encoding="utf-8")
            geom_path.write_text(json.dumps(_geom()), encoding="utf-8")
            with self.assertRaises(ValueError):
                build_payload(coeff_path, geom_path, out_path)


if __name__ == "__main__":
    unittest.main()
