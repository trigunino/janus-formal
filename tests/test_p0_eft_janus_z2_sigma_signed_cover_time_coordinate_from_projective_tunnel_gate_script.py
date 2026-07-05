import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate import (
    build_payload,
)


class SignedCoverTimeCoordinateFromProjectiveTunnelGateTests(unittest.TestCase):
    def test_projective_tunnel_writes_odd_signed_cover_time_coordinate(self):
        with tempfile.TemporaryDirectory() as tmp:
            output_path = Path(tmp) / "signed_time.json"
            payload = build_payload(output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["projective_tunnel_closed"])
        self.assertEqual(payload["antipodal_pullback"], "minus_self")
        self.assertEqual(written["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            written["signed_cover_time_coordinate"]["antipodal_pullback"],
            "minus_self",
        )
        self.assertFalse(written["archived_z4_background_reuse_used"])
        self.assertFalse(written["observational_time_gauge_fit_used"])


if __name__ == "__main__":
    unittest.main()
