import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_pt_souriau_omega_from_theta_gate import build_payload


class PTSouriauOmegaFromThetaGateTests(unittest.TestCase):
    def test_live_theta_route_is_trivial_or_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["theta_input_exists"])
        self.assertFalse(payload["integrality_route_open"])

    def test_nontrivial_theta_writes_integrality_skeleton(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            theta = root / "theta.json"
            out = root / "integrality.json"
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

            payload = build_payload(theta_path=theta, output_path=out, write_output=True)
            written = out.exists()

        self.assertTrue(payload["integrality_route_open"])
        self.assertTrue(written)


if __name__ == "__main__":
    unittest.main()
