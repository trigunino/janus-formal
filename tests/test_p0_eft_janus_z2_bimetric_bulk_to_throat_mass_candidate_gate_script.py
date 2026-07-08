import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_throat_mass_candidate_gate import (
    build_payload,
)


def _projection_payload() -> dict:
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


def _global_mass_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "stress_energy_state_proved": True,
        "PT_energy_sign_reversal_proved": True,
        "M_plus_kg": 2.0,
        "state_provenance": "active_global_bimetric_state",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


class BimetricBulkToThroatMassCandidateGateTests(unittest.TestCase):
    def test_default_workspace_stays_relative_only_if_no_mass_state(self):
        payload = build_payload(write_output=False)

        self.assertTrue(payload["published_relative_bimetric_structure_ready"])
        self.assertFalse(payload["mass_interpretation"]["relative_bimetric_ratios_alone_fix_mass"])

    def test_valid_bulk_and_projection_close_strict_throat_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            projection_path = base / "projection.json"
            global_mass_path = base / "global_mass.json"
            projection_path.write_text(json.dumps(_projection_payload()), encoding="utf-8")
            global_mass_path.write_text(json.dumps(_global_mass_payload()), encoding="utf-8")

            payload = build_payload(
                projection_path=projection_path,
                global_mass_input_path=global_mass_path,
                global_solution_path=base / "solution.json",
                mass_charge_path=base / "bridge.json",
                write_output=True,
            )

        self.assertTrue(payload["global_bulk_mass_route_ready"])
        self.assertTrue(payload["sigma_pt_projection_route_ready"])
        self.assertTrue(payload["strict_throat_mass_ready"])
        self.assertEqual(payload["M_bridge_kg"], 2.0)


if __name__ == "__main__":
    unittest.main()
