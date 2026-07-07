import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_moebius_twisted_cycle_alpha_route_gate import build_payload


class MoebiusTwistedCycleAlphaRouteGateTests(unittest.TestCase):
    def test_live_moebius_route_is_not_alpha_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["twisted_2d_shadow_ready"])
        self.assertTrue(payload["z2_orientation_reversing_cycle_ready"])
        self.assertFalse(payload["theta_period_nonzero"])
        self.assertFalse(payload["compact_action_cycle_ready"])
        self.assertFalse(payload["alpha_selector_ready"])

    def test_nonzero_theta_still_needs_compact_action_cycle(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            projective = root / "projective.json"
            theta = root / "theta.json"
            projective.write_text(
                json.dumps(
                    {
                        "projective_tunnel_topology": {
                            "torus_to_klein_two_fold_cover": True,
                            "resolved_tunnel_shadow_not_boy_surface": True,
                        },
                        "projective_tunnel_interface": {
                            "around_sigma_cycle_defined": True,
                            "around_sigma_maps_to_generator": True,
                        },
                        "z2_holonomy_path_available": True,
                    }
                ),
                encoding="utf-8",
            )
            theta.write_text(
                json.dumps(
                    {
                        "R_h_trace_values_ready": True,
                        "R_K_trace_values_ready": True,
                        "R_h_trace_values": [1.0],
                        "R_K_trace_values": [0.0],
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(projective, theta)

        self.assertTrue(payload["theta_period_nonzero"])
        self.assertFalse(payload["compact_action_cycle_ready"])
        self.assertFalse(payload["alpha_selector_ready"])


if __name__ == "__main__":
    unittest.main()
