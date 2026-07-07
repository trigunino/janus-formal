import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload,
)


class PublishedGlobalEnergyConstantRouteGateTests(unittest.TestCase):
    def test_live_route_blocks_without_global_energy_input(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "missing_published_global_energy_constant_inputs",
            payload["validation_errors"],
        )
        self.assertIn("Archived Z4", payload["why_Z4_did_not_solve_this"])

    def test_computes_density_from_global_energy_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "energy.json"
            ratio_path = root / "ratio.json"
            output_path = root / "out.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "published_janus_exact_global_energy_state",
                        "global_energy_constant_proved": True,
                        "global_energy_provenance": "published_exact_bimetric_FLRW_energy_constant",
                        "E_global_J": 10.0,
                        "c_plus0_m_s": 1.0,
                        "c_minus0_m_s": 1.0,
                        "a_plus0_weight": 4.0,
                        "a_minus0_weight": 1.0,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            ratio_path.write_text(
                json.dumps({"rho_minus0_over_rho_plus0": -1.0}),
                encoding="utf-8",
            )

            payload = build_payload(
                input_path=input_path,
                ratio_path=ratio_path,
                output_path=output_path,
                write_output=True,
            )

            self.assertTrue(payload["gate_passed"])
            self.assertAlmostEqual(
                payload["normalized_sector_payload"]["rho_plus0_abs_kg_m3"],
                10.0 / 3.0,
            )
            self.assertTrue(output_path.exists())


if __name__ == "__main__":
    unittest.main()
