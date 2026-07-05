import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_sector_four_velocity_from_time_direction_gate import (
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


def _metric(**overrides):
    payload = _base()
    payload.update(
        {
            "sector_metric_on_sigma_ready": True,
            "metric_plus_munu_values": [[[-4.0, 0.0], [0.0, 1.0]], [[-9.0, 0.0], [0.0, 1.0]]],
            "metric_minus_munu_values": [[[-16.0, 0.0], [0.0, 1.0]], [[-25.0, 0.0], [0.0, 1.0]]],
        }
    )
    payload.update(overrides)
    return payload


def _time_direction(**overrides):
    payload = _base()
    payload.update(
        {
            "sector_time_direction_on_sigma_ready": True,
            "time_direction_plus_values": [[1.0, 0.0], [1.0, 0.0]],
            "time_direction_minus_values": [[1.0, 0.0], [1.0, 0.0]],
        }
    )
    payload.update(overrides)
    return payload


class SectorFourVelocityFromTimeDirectionGateTests(unittest.TestCase):
    def test_writes_normalized_four_velocities(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            time_direction = root / "time.json"
            output = root / "velocity.json"
            metric.write_text(json.dumps(_metric()), encoding="utf-8")
            time_direction.write_text(json.dumps(_time_direction()), encoding="utf-8")

            payload = build_payload(
                metric_path=metric,
                time_direction_path=time_direction,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["sector_four_velocity_on_sigma_ready"])
        self.assertEqual(written["u_plus_contravariant_values"], [[0.5, 0.0], [1.0 / 3.0, 0.0]])
        self.assertEqual(written["u_minus_contravariant_values"], [[0.25, 0.0], [0.2, 0.0]])

    def test_missing_time_direction_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            metric.write_text(json.dumps(_metric()), encoding="utf-8")

            payload = build_payload(
                metric_path=metric,
                time_direction_path=root / "missing.json",
                output_path=root / "velocity.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "sector_time_direction_on_sigma_inputs")

    def test_spacelike_direction_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            time_direction = root / "time.json"
            metric.write_text(json.dumps(_metric()), encoding="utf-8")
            bad = _time_direction(time_direction_plus_values=[[0.0, 1.0], [1.0, 0.0]])
            time_direction.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(
                metric_path=metric,
                time_direction_path=time_direction,
                output_path=root / "velocity.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("timelike", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
