import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_exact_solution_alpha_state_sector_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate import (
    build_payload as build_alpha_to_energy,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as build_global_energy_normalization,
)
from scripts.build_p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate import (
    build_payload as build_density_pressure,
)


class ExactSolutionAlphaStateSectorGateTests(unittest.TestCase):
    def test_live_gate_blocks_without_input(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["remaining_blocker"], "alpha_state_sector_input")

    def test_rejects_observational_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "state.json"
            out = root / "scale.json"
            inp.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "exact_solution_integration_constant_state",
                        "alpha_m": 1.0,
                        "alpha_state_provenance": "Planck fit",
                        "alpha_sector_declared_not_derived": True,
                        "full_no_fit_prediction_ready": False,
                        "c_plus0_m_s": 3.0,
                        "c_minus0_m_s": 3.0,
                        "G_plus_SI": 5.0,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("alpha_state_provenance_missing_or_forbidden", payload["validation_errors"])

    def test_writes_scale_input_from_state_sector(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "state.json"
            out = root / "scale.json"
            inp.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "exact_solution_integration_constant_state",
                        "alpha_m": 2.0,
                        "alpha_state_provenance": "global_souriau_sector",
                        "alpha_sector_declared_not_derived": True,
                        "full_no_fit_prediction_ready": False,
                        "c_plus0_m_s": 3.0,
                        "c_minus0_m_s": 4.0,
                        "G_plus_SI": 5.0,
                        "a_plus0_weight": 1.5,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["alpha_is_integration_constant"])
        self.assertFalse(written["full_no_fit_prediction_ready"])

    def test_alpha_state_sector_feeds_density_route(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state = root / "state.json"
            scale = root / "scale.json"
            energy = root / "energy.json"
            ratio = root / "ratio.json"
            norm = root / "norm.json"
            grid = root / "grid.json"
            density = root / "density.json"
            state.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "exact_solution_integration_constant_state",
                        "alpha_m": 2.0,
                        "alpha_state_provenance": "global_souriau_sector",
                        "alpha_sector_declared_not_derived": True,
                        "full_no_fit_prediction_ready": False,
                        "c_plus0_m_s": 3.0,
                        "c_minus0_m_s": 3.0,
                        "G_plus_SI": 5.0,
                        "a_plus0_weight": 1.0,
                        "a_minus0_weight": 2.0,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            ratio.write_text(json.dumps({"rho_minus0_over_rho_plus0": -1.0}), encoding="utf-8")
            grid.write_text(json.dumps({"a_grid": [1.0, 2.0]}), encoding="utf-8")

            state_payload = build_payload(input_path=state, output_path=scale, write_output=True)
            energy_payload = build_alpha_to_energy(
                input_path=scale,
                output_path=energy,
                write_output=True,
            )
            norm_payload = build_global_energy_normalization(
                input_path=energy,
                ratio_path=ratio,
                output_path=norm,
                write_output=True,
            )
            density_payload = build_density_pressure(
                rho_path=root / "missing-rho.json",
                global_energy_normalization_path=norm,
                grid_path=grid,
                output_path=density,
            )

        self.assertTrue(state_payload["gate_passed"])
        self.assertTrue(energy_payload["gate_passed"])
        self.assertTrue(norm_payload["gate_passed"])
        self.assertTrue(density_payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
