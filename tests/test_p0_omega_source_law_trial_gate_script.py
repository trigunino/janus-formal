from __future__ import annotations

import unittest

from scripts.build_p0_omega_source_law_trial_gate import build_payload


class P0OmegaSourceLawTrialGateTests(unittest.TestCase):
    def test_source_law_trial_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-source-law-trial-open")
        self.assertTrue(payload["fermi_walker_trial_available"])
        self.assertTrue(payload["fermi_walker_omega_u_zero_trial_available"])
        self.assertTrue(payload["source_congruence_trial_available"])
        self.assertTrue(payload["source_congruence_omega_gate_available"])
        self.assertTrue(payload["shared_transport_required"])
        self.assertTrue(payload["no_gauge_fit_rule_closed"])
        self.assertFalse(payload["source_law_closed"])
        self.assertTrue(payload["omega_source_or_axiom_decision_available"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_trials_cover_fw_congruence_shared_transport_and_no_fit(self) -> None:
        text = " ".join(row["trial"] + row["condition"] for row in build_payload()["trial_rows"])

        self.assertIn("fermi_walker", text)
        self.assertIn("Omega_u u=0", text)
        self.assertIn("source_congruence", text)
        self.assertIn("K, Q_cross, and mirror", text)
        self.assertIn("after residual evaluation", text)


if __name__ == "__main__":
    unittest.main()
