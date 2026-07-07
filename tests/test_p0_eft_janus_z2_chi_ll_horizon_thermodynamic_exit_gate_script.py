import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import build_payload


class ChiLLHorizonThermodynamicExitGateTests(unittest.TestCase):
    def test_default_blocks_without_horizon_inputs(self):
        payload = build_payload(Path("missing-horizon-input.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["horizon_thermodynamic_exit_ready"])
        self.assertIn("Sigma_PT_is_null_horizon", payload["blocked_by"])
        self.assertIn("R_s_m", payload["blocked_by"])

    def test_forbidden_shortcuts_are_explicit(self):
        shortcuts = build_payload(Path("missing-horizon-input.json"))["forbidden_shortcuts"]

        self.assertTrue(shortcuts["declare_horizon_without_null_expansion_or_boundary_data"])
        self.assertTrue(shortcuts["choose_surface_gravity_normalization_by_fit"])
        self.assertTrue(shortcuts["use_entropy_extremum_without_first_law"])

    def test_closes_conditionally_with_complete_horizon_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "horizon.json"
            path.write_text(
                json.dumps(
                    {
                        "Sigma_PT_is_null_horizon": True,
                        "surface_gravity_kappa_l_1_per_m": 0.25,
                        "R_s_m": 2.0,
                        "entropy_law": "Bekenstein_Hawking_area",
                        "temperature_law": "T=hbar*c*kappa_l/(2*pi*kB)",
                        "energy_law": "Misner_Sharp_horizon_mass",
                        "first_law_or_unified_first_law_declared": True,
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["horizon_thermodynamic_exit_ready"])
        self.assertTrue(payload["chi_LL_prediction_ready"])
        self.assertAlmostEqual(
            payload["derivation"]["chi_LL_abs_inverse_m"],
            1.0 / (8.0 * math.pi * 2.0),
        )


if __name__ == "__main__":
    unittest.main()
