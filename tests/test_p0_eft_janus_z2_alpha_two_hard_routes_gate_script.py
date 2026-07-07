import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_alpha_two_hard_routes_gate import build_payload


class AlphaTwoHardRoutesGateTests(unittest.TestCase):
    def test_live_routes_do_not_generate_alpha(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["alpha_generated"])
        self.assertEqual(
            payload["pt_holonomy_route"]["verdict"], "closed_zero_on_current_branch"
        )
        self.assertEqual(payload["valpha_route"]["verdict"], "blocked_before_on_shell_action")

    def test_nonzero_theta_or_ready_hamiltonian_reopens_routes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            theta = root / "theta.json"
            ham = root / "ham.json"
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
            ham.write_text(
                json.dumps(
                    {
                        "canonical_hamiltonian_reduction_ready": True,
                        "checks": {
                            "symplectic_pullback_to_exact_solution_derived": True
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(theta, ham)

        self.assertTrue(payload["alpha_generated"])
        self.assertTrue(payload["pt_holonomy_route"]["holonomy_phase_from_theta_ready"])
        self.assertTrue(payload["valpha_route"]["V_alpha_ready"])


if __name__ == "__main__":
    unittest.main()
