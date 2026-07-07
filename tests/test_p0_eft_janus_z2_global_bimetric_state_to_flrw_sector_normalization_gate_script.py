import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate import (
    build_payload,
)


class GlobalBimetricStateToFLRWSectorNormalizationGateTests(unittest.TestCase):
    def test_blocks_without_global_state(self):
        payload = build_payload(input_path=Path("missing.json"))

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["sector_normalizations_ready"])
        self.assertEqual(payload["primary_blocker"], "missing_global_bimetric_stress_energy_state_inputs")

    def test_derives_sector_normalizations_from_active_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.json"
            out = Path(tmp) / "sector.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "stress_energy_state_proved": True,
                        "PT_energy_sign_reversal_proved": True,
                        "rho_plus0_abs_kg_m3": 4.0,
                        "rho_minus0_abs_kg_m3": -76.0,
                        "rho_minus0_over_rho_plus0": -19.0,
                        "state_provenance": "active_global_bimetric_noether_state",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=path, output_path=out, write_output=True)

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["normalized_sector_payload"]["rho_plus0_kg_m3"], 4.0)
        self.assertEqual(payload["normalized_sector_payload"]["rho_plus0_abs_kg_m3"], 4.0)
        self.assertEqual(payload["normalized_sector_payload"]["rho_minus0_kg_m3"], -76.0)
        self.assertEqual(payload["normalized_sector_payload"]["rho_minus0_over_rho_plus0"], -19.0)

    def test_rejects_fit_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "stress_energy_state_proved": True,
                        "PT_energy_sign_reversal_proved": True,
                        "rho_plus_kg_m3": 4.0,
                        "state_provenance": "Planck fit",
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("state_provenance_missing_or_forbidden", payload["validation_errors"])


if __name__ == "__main__":
    unittest.main()
