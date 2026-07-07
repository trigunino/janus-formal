import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate import (
    build_payload,
)


class RhoPlus0AbsSymbolicClosureGateTests(unittest.TestCase):
    def test_blocks_without_independent_state_and_radius_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                constants_path=root / "constants.json",
                occupation_path=root / "occupation.json",
                radius_path=root / "radius.json",
                sector_ratio_path=root / "ratio.json",
                output_path=root / "rho.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["bottom_reached_without_extension"])
        self.assertIn("N_occ_Z2Sigma", payload["remaining_independent_inputs"])
        self.assertIn("R_curv_Z2Sigma", payload["remaining_independent_inputs"])

    def test_computes_rho_plus0_abs_from_state_radius_and_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            constants = root / "constants.json"
            occupation = root / "occupation.json"
            radius = root / "radius.json"
            ratio = root / "ratio.json"
            output = root / "rho.json"
            constants.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "constants": {"baryon_mass_kg": 2.0},
                    }
                ),
                encoding="utf-8",
            )
            occupation.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "explicit_state_initial_data",
                        "full_no_fit_prediction_ready": False,
                        "N_occ_Z2Sigma": 3.0,
                        "N_occ_provenance": "declared_superselection_state_initial_data",
                    }
                ),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scalars": {"R_curv_Z2Sigma_m": 4.0},
                        "scalar_provenance": {
                            "R_curv_Z2Sigma": "active_geometry_radius"
                        },
                    }
                ),
                encoding="utf-8",
            )
            ratio.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "normalizations": {"rho_minus0_over_rho_plus0": -19.0},
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                constants_path=constants,
                occupation_path=occupation,
                radius_path=radius,
                sector_ratio_path=ratio,
                output_path=output,
            )

            expected = 2.0 * 3.0 / (math.pi**2 * 4.0**3)
            self.assertTrue(payload["gate_passed"])
            self.assertAlmostEqual(payload["rho_plus0_abs_kg_m3"], expected)
            self.assertAlmostEqual(payload["rho_minus0_abs_kg_m3"], -19.0 * expected)
            self.assertTrue(output.exists())


if __name__ == "__main__":
    unittest.main()
