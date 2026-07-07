import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate import (
    build_payload,
)


class SectorDensityPressureFromRhoPlus0AbsGateTests(unittest.TestCase):
    def test_blocks_until_rho_plus0_abs_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            grid = root / "grid.json"
            grid.write_text(json.dumps({"a_grid": [0.5, 1.0]}), encoding="utf-8")
            payload = build_payload(
                rho_path=root / "missing.json",
                grid_path=grid,
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("rho_plus0_abs_or_global_energy_normalization_not_ready", payload["blocked_by"])

    def test_writes_dust_density_pressure_from_ready_rho(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rho = root / "rho.json"
            grid = root / "grid.json"
            out = root / "out.json"
            rho.write_text(
                json.dumps(
                    {
                        "rho_plus0_abs_ready": True,
                        "rho_plus0_abs_kg_m3": 2.0,
                        "rho_minus0_abs_kg_m3": -38.0,
                        "rho_minus0_over_rho_plus0": -19.0,
                    }
                ),
                encoding="utf-8",
            )
            grid.write_text(json.dumps({"a_grid": [0.5, 1.0]}), encoding="utf-8")

            payload = build_payload(rho_path=rho, grid_path=grid, output_path=out)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["rho_plus_values"], [16.0, 2.0])
        self.assertEqual(written["rho_minus_values"], [-304.0, -38.0])
        self.assertEqual(written["p_plus_values"], [0.0, 0.0])

    def test_writes_from_global_energy_normalization_when_local_rho_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            norm = root / "norm.json"
            grid = root / "grid.json"
            out = root / "out.json"
            norm.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived_from_published_global_energy_constant",
                        "rho_plus0_abs_kg_m3": 2.0,
                        "rho_minus0_abs_kg_m3": -38.0,
                        "rho_minus0_over_rho_plus0": -19.0,
                    }
                ),
                encoding="utf-8",
            )
            grid.write_text(json.dumps({"a_grid": [1.0, 2.0]}), encoding="utf-8")

            payload = build_payload(
                rho_path=root / "missing.json",
                global_energy_normalization_path=norm,
                grid_path=grid,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["normalization_kind"], "published_global_energy_constant")
        self.assertEqual(written["rho_plus_values"], [2.0, 0.25])


if __name__ == "__main__":
    unittest.main()
