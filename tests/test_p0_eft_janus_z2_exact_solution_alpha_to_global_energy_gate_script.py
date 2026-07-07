import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate import (
    build_payload,
    global_energy_mass_from_alpha,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as build_global_energy_normalization,
)
from scripts.build_p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate import (
    build_payload as build_density_pressure,
)


class ExactSolutionAlphaToGlobalEnergyGateTests(unittest.TestCase):
    def test_mass_formula(self):
        self.assertAlmostEqual(
            global_energy_mass_from_alpha(2.0, 3.0, 5.0),
            -(2.0 * 9.0) / (2.0 * math.pi * 5.0),
        )

    def test_live_gate_blocks_without_alpha(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["remaining_blocker"],
            "alpha_m_from_non_observational_global_clock",
        )

    def test_writes_global_energy_input_from_alpha(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "alpha.json"
            out = root / "energy.json"
            inp.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scale_provenance": "published_exact_solution_alpha_from_global_clock",
                        "alpha_m": 2.0,
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

            self.assertTrue(payload["gate_passed"])
            self.assertTrue(out.exists())
            self.assertLess(payload["global_energy_payload"]["E_global_J"], 0.0)

    def test_alpha_route_can_feed_sector_density_without_local_occupation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            alpha = root / "alpha.json"
            energy = root / "energy.json"
            ratio = root / "ratio.json"
            norm = root / "norm.json"
            grid = root / "grid.json"
            density = root / "density.json"
            alpha.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scale_provenance": "published_exact_solution_alpha_from_global_clock",
                        "alpha_m": 2.0,
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
            ratio.write_text(
                json.dumps({"rho_minus0_over_rho_plus0": -1.0}),
                encoding="utf-8",
            )
            grid.write_text(json.dumps({"a_grid": [1.0, 2.0]}), encoding="utf-8")

            alpha_payload = build_payload(input_path=alpha, output_path=energy, write_output=True)
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

        self.assertTrue(alpha_payload["gate_passed"])
        self.assertTrue(norm_payload["gate_passed"])
        self.assertTrue(density_payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
