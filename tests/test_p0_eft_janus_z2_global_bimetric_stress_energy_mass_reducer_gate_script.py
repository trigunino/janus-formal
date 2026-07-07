import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate import (
    build_payload,
)


class GlobalBimetricStressEnergyMassReducerGateTests(unittest.TestCase):
    def test_blocks_without_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["global_stress_energy_mass_available"])
        self.assertIn("derive_global_bimetric_stress_energy_state", payload["next_required"])

    def test_reduces_density_volume_to_global_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "state.json"
            input_path.write_text(
                """{
  "active_core": "Z2_tunnel_Sigma",
  "source": "active_derived",
  "stress_energy_state_proved": true,
  "PT_energy_sign_reversal_proved": true,
  "rho_plus_kg_m3": 2.0,
  "V_plus_m3": 3.0,
  "state_provenance": "active_global_bimetric_state",
  "observational_fit_used": false,
  "compressed_planck_lcdm_background_used": false,
  "archived_z4_reuse_used": false
}""",
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["global_mass_payload"]["M_plus_kg"], 6.0)
        self.assertEqual(payload["global_mass_payload"]["M_minus_kg"], -6.0)


if __name__ == "__main__":
    unittest.main()
