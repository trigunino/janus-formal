import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_bimetric_vacuum_alpha_selector_gate import build_payload


class BimetricVacuumAlphaSelectorGateTests(unittest.TestCase):
    def test_live_bimetric_vacuum_route_is_not_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["published_relative_sector_ratio_ready"])
        self.assertFalse(payload["absolute_density_scale_ready"])
        self.assertFalse(payload["alpha_selector_ready"])
        self.assertIn("rho_plus0_abs_ready", payload["blocked_by"])

    def test_complete_synthetic_state_law_selects_alpha(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ratio = root / "ratio.json"
            rho = root / "rho.json"
            state = root / "state.json"
            ratio.write_text(
                json.dumps({"relative_sector_ratio_ready": True, "absolute_density_scale_ready": True}),
                encoding="utf-8",
            )
            rho.write_text(
                json.dumps({"rho_plus0_abs_ready": True, "remaining_independent_inputs": []}),
                encoding="utf-8",
            )
            state.write_text(
                json.dumps({"sector_normalizations_ready": True}),
                encoding="utf-8",
            )

            payload = build_payload(ratio, rho, state)

        self.assertTrue(payload["alpha_selector_ready"])
        self.assertEqual(payload["blocked_by"], [])


if __name__ == "__main__":
    unittest.main()
