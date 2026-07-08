import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_mass_state_from_exact_global_energy_volume_gate import (
    build_payload,
)


class GlobalMassStateFromExactGlobalEnergyVolumeGateTests(unittest.TestCase):
    def test_blocks_without_energy_and_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                energy_path=base / "energy.json",
                volume_path=base / "volume.json",
                output_path=base / "state.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["global_mass_state_ready"])
        self.assertIn("missing_global_energy_constant_sector_normalization_inputs", payload["validation_errors"])

    def test_builds_mass_state_from_energy_density_and_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            energy = base / "energy.json"
            volume = base / "volume.json"
            energy.write_text(
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
            volume.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "normalizations": {"spatial_volume0_m3_Z2Sigma": 5.0},
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                energy_path=energy,
                volume_path=volume,
                output_path=base / "state.json",
                write_output=True,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["state_payload"]["M_plus_kg"], 10.0)


if __name__ == "__main__":
    unittest.main()
