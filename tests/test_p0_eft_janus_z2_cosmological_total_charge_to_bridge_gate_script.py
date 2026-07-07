import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_cosmological_total_charge_to_bridge_gate import (
    build_payload,
)


def projection_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "visible_charge_conserved_to_Sigma": True,
        "Sigma_projection_complete": True,
        "Q_Sigma_equals_M_bridge_c2": True,
        "projection_factor_to_bridge": 1.0,
        "projection_provenance": "active_cosmological_charge_projection",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


def global_mass_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "stress_energy_state_proved": True,
        "PT_energy_sign_reversal_proved": True,
        "M_plus_kg": 2.0,
        "state_provenance": "active_global_visible_charge",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


class CosmologicalTotalChargeToBridgeGateTests(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                projection_path=base / "projection.json",
                global_mass_path=base / "global.json",
                global_solution_path=base / "solution.json",
                mass_charge_path=base / "bridge.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["projection_ready"])
        self.assertFalse(payload["global_mass_ready"])

    def test_valid_projection_and_mass_writes_bridge(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            projection_path = base / "projection.json"
            global_path = base / "global.json"
            solution_path = base / "solution.json"
            bridge_path = base / "bridge.json"
            projection_path.write_text(json.dumps(projection_payload()), encoding="utf-8")
            global_path.write_text(json.dumps(global_mass_payload()), encoding="utf-8")
            payload = build_payload(
                projection_path=projection_path,
                global_mass_path=global_path,
                global_solution_path=solution_path,
                mass_charge_path=bridge_path,
                write_output=True,
            )
            self.assertTrue(solution_path.exists())
            self.assertTrue(bridge_path.exists())

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["bridge_payload"]["M_bridge_kg"], 2.0)

    def test_projection_factor_scales_bridge_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            projection = projection_payload()
            projection["projection_factor_to_bridge"] = 0.25
            projection_path = base / "projection.json"
            global_path = base / "global.json"
            projection_path.write_text(json.dumps(projection), encoding="utf-8")
            global_path.write_text(json.dumps(global_mass_payload()), encoding="utf-8")
            payload = build_payload(
                projection_path=projection_path,
                global_mass_path=global_path,
                global_solution_path=base / "solution.json",
                mass_charge_path=base / "bridge.json",
                write_output=True,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["bridge_payload"]["M_bridge_kg"], 0.5)


if __name__ == "__main__":
    unittest.main()
