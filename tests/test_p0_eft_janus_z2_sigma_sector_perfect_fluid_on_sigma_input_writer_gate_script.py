import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_sector_perfect_fluid_on_sigma_input_writer_gate import (
    build_payload,
)


def _base():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": [0.5, 1.0],
    }


def _density_pressure(**overrides):
    payload = _base()
    payload.update(
        {
            "sector_density_pressure_on_sigma_ready": True,
            "rho_plus_values": [10.0, 20.0],
            "p_plus_values": [2.0, 4.0],
            "rho_minus_values": [3.0, 5.0],
            "p_minus_values": [1.0, 2.0],
        }
    )
    payload.update(overrides)
    return payload


def _metric(**overrides):
    payload = _base()
    payload.update(
        {
            "sector_metric_on_sigma_ready": True,
            "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
            "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
        }
    )
    payload.update(overrides)
    return payload


def _velocity(**overrides):
    payload = _base()
    payload.update(
        {
            "sector_four_velocity_on_sigma_ready": True,
            "u_plus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
            "u_minus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
        }
    )
    payload.update(overrides)
    return payload


class SectorPerfectFluidOnSigmaInputWriterGateTests(unittest.TestCase):
    def test_writes_sector_perfect_fluid_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            metric = root / "metric.json"
            velocity = root / "velocity.json"
            output = root / "fluid.json"
            density.write_text(json.dumps(_density_pressure()), encoding="utf-8")
            metric.write_text(json.dumps(_metric()), encoding="utf-8")
            velocity.write_text(json.dumps(_velocity()), encoding="utf-8")

            payload = build_payload(
                density_pressure_path=density,
                metric_path=metric,
                velocity_path=velocity,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["sector_perfect_fluid_on_sigma_ready"])
        self.assertEqual(written["rho_plus_values"], [10.0, 20.0])
        self.assertEqual(written["metric_plus_munu_values"][0], [[-1.0, 0.0], [0.0, 1.0]])
        self.assertEqual(written["u_minus_contravariant_values"][1], [1.0, 0.0])

    def test_missing_metric_reports_exact_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            velocity = root / "velocity.json"
            density.write_text(json.dumps(_density_pressure()), encoding="utf-8")
            velocity.write_text(json.dumps(_velocity()), encoding="utf-8")

            payload = build_payload(
                density_pressure_path=density,
                metric_path=root / "missing.json",
                velocity_path=velocity,
                output_path=root / "fluid.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "sector_metric_on_sigma_inputs")

    def test_forbidden_density_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            metric = root / "metric.json"
            velocity = root / "velocity.json"
            density.write_text(
                json.dumps(_density_pressure(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )
            metric.write_text(json.dumps(_metric()), encoding="utf-8")
            velocity.write_text(json.dumps(_velocity()), encoding="utf-8")

            payload = build_payload(
                density_pressure_path=density,
                metric_path=metric,
                velocity_path=velocity,
                output_path=root / "fluid.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
