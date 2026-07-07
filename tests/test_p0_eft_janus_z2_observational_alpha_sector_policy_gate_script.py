import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_observational_alpha_sector_policy_gate import build_payload


class ObservationalAlphaSectorPolicyGateTests(unittest.TestCase):
    def test_live_policy_is_observational_not_no_fit(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["no_fit_prediction"])
        self.assertEqual(payload["classification"], "observational_sector_selection_not_no_fit")
        self.assertIn("SN_Ia", payload["recommended_minimal_fit"])
        self.assertIn("BAO", payload["recommended_minimal_fit"])

    def test_sn_only_does_not_break_absolute_scale(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "baseline.md"
            path.write_text("Pantheon+ only", encoding="utf-8")

            payload = build_payload(path)

        self.assertTrue(payload["alpha_sector_observable"])
        self.assertFalse(payload["absolute_scale_breaking_possible"])
        self.assertFalse(payload["no_fit_prediction"])


if __name__ == "__main__":
    unittest.main()
