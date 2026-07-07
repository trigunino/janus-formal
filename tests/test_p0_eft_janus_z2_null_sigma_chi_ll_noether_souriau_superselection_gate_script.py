import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate import (
    build_payload,
)


class ChiLLNoetherSouriauSuperselectionGateTests(unittest.TestCase):
    def test_missing_orbit_state_blocks_without_selecting_chi(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                input_path=base / "missing.json",
                output_path=base / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["souriau_superselection_route_formulated"])
        self.assertFalse(payload["souriau_superselection_selects_chi_LL_now"])
        self.assertIn("derive_or_declare_active_Souriau_orbit_state_with_mass_casimir_kg", payload["next_required"])

    def test_forbidden_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            path = base / "state.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "orbit_label_kind": "coadjoint_orbit_mass_casimir",
                        "moment_map_conserved": True,
                        "PT_energy_sign_reversal_proved": True,
                        "mass_casimir_kg": 2.0,
                        "orbit_state_provenance": "fit-derived",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=path, output_path=base / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("orbit_state_provenance_missing_or_forbidden", payload["validation_errors"])

    def test_valid_orbit_state_writes_global_mass_solution_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            path = base / "state.json"
            output = base / "mass.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "orbit_label_kind": "global_hamiltonian_moment_map",
                        "moment_map_conserved": True,
                        "PT_energy_sign_reversal_proved": True,
                        "mass_casimir_kg": 3.5,
                        "orbit_state_provenance": "active_souriau_orbit_certificate",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=path, output_path=output, write_output=True)
            self.assertTrue(output.exists())
            mass_payload = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(mass_payload["M_plus_kg"], 3.5)
        self.assertEqual(mass_payload["M_minus_kg"], -3.5)


if __name__ == "__main__":
    unittest.main()
