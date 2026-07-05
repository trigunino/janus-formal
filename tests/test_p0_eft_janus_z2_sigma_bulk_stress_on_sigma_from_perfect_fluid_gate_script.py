import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_on_sigma_from_perfect_fluid_gate import (
    build_payload,
)


def _source(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "sector_perfect_fluid_on_sigma_ready": True,
        "a_grid": [0.5, 1.0],
        "rho_plus_values": [10.0, 20.0],
        "p_plus_values": [2.0, 4.0],
        "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
        "u_plus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
        "rho_minus_values": [3.0, 5.0],
        "p_minus_values": [1.0, 2.0],
        "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
        "u_minus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
    }
    payload.update(overrides)
    return payload


class BulkStressOnSigmaFromPerfectFluidGateTests(unittest.TestCase):
    def test_writes_bulk_stress_on_sigma(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.json"
            output = root / "stress.json"
            source.write_text(json.dumps(_source()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["bulk_stress_on_sigma_ready"])
        self.assertEqual(written["T_plus_munu_values"][0], [[10.0, 0.0], [0.0, 2.0]])
        self.assertEqual(written["T_minus_munu_values"][1], [[5.0, 0.0], [0.0, 2.0]])

    def test_missing_source_blocks_on_perfect_fluid_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "sector_perfect_fluid_on_sigma_inputs")

    def test_forbidden_fit_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.json"
            bad = _source(observational_H0_fit_used=True)
            source.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=root / "stress.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
