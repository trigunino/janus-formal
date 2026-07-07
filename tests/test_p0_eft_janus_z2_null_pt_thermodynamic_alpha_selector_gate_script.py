import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_pt_thermodynamic_alpha_selector_gate import build_payload


class NullPTThermodynamicAlphaSelectorGateTests(unittest.TestCase):
    def test_live_null_thermodynamic_route_is_not_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["null_PT_bridge_context_available"])
        self.assertFalse(payload["alpha_selector_ready"])
        self.assertIn("proved_horizon_status", payload["blocked_by"])
        self.assertIn("chi_LL_selected", payload["blocked_by"])

    def test_complete_synthetic_thermodynamic_route_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            horizon = root / "horizon.json"
            null_branch = root / "null.json"
            llbrane = root / "llbrane.json"
            horizon.write_text(
                json.dumps(
                    {
                        "checks": {
                            "proved_horizon_status": True,
                            "kappa_l_available": True,
                            "entropy_law_declared": True,
                            "temperature_law_declared": True,
                            "first_law_energy_definition_available": True,
                        }
                    }
                ),
                encoding="utf-8",
            )
            null_branch.write_text(
                json.dumps({"branch": "Z2_null_Sigma_PT_bridge"}),
                encoding="utf-8",
            )
            llbrane.write_text(
                json.dumps({"chi_LL_derivation_ready": True}),
                encoding="utf-8",
            )

            payload = build_payload(horizon, null_branch, llbrane)

        self.assertTrue(payload["alpha_selector_ready"])
        self.assertEqual(payload["blocked_by"], [])


if __name__ == "__main__":
    unittest.main()
