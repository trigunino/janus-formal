import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_action_onshell_alpha_selector_gate import build_payload


class GlobalActionOnshellAlphaSelectorGateTests(unittest.TestCase):
    def test_live_action_route_is_not_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["published_bimetric_action_anchor_available"])
        self.assertTrue(payload["exact_alpha_family_available"])
        self.assertFalse(payload["alpha_selector_ready"])
        self.assertIn("on_shell_S_or_V_alpha_derived", payload["blocked_by"])

    def test_complete_synthetic_selector_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mini = root / "mini.json"
            scouple = root / "scouple.json"
            mini.write_text(
                json.dumps(
                    {
                        "checks": {
                            "published_exact_solution_available": True,
                            "alpha_Eglobal_identity_available": True,
                            "minisuperspace_lagrangian_written": True,
                            "action_integral_I_alpha_derived": True,
                            "compact_cycle_in_reduced_orbit_found": True,
                            "integrality_or_selection_law_derived": True,
                        }
                    }
                ),
                encoding="utf-8",
            )
            scouple.write_text(
                json.dumps({"m15_action_accepted_for_field_equations": True}),
                encoding="utf-8",
            )

            payload = build_payload(mini, scouple)

        self.assertTrue(payload["alpha_selector_ready"])
        self.assertEqual(payload["blocked_by"], [])


if __name__ == "__main__":
    unittest.main()
