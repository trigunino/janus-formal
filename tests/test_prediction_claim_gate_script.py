from __future__ import annotations

import unittest

from scripts.build_prediction_claim_gate import build_payload


READY_PHYSICAL_ROLLUP = {
    "all_terminal_blockers_closed": True,
    "physics_closed": True,
    "prediction_ready": True,
    "open_terminal_blockers": [],
}


class PredictionClaimGateTests(unittest.TestCase):
    def test_gate_blocks_prediction_when_scaffolds_remain(self) -> None:
        payload = build_payload(
            lensing={
                "gates": [
                    {
                        "gate": "Q_det convention",
                        "status": "partial",
                        "blocks_s8": True,
                    }
                ]
            },
            scaffolds={
                "tracks": [
                    {"track": "Bianchi closure"},
                    {"track": "Q_cross"},
                ]
            },
            observable_chain={"blocking_issue": True},
            survey_interface={"boundary": "Interface only. No survey result."},
            ic_source_targets={
                "missing_source_targets": [
                    {"target": "transfer", "blocks_final_ic": True}
                ]
            },
            pm_band_limited={"blocking_issue": True},
            physical_rollup=READY_PHYSICAL_ROLLUP,
        )

        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(payload["allowed_claim_level"], "diagnostic")
        self.assertIn("Q_det convention", payload["blockers"])
        self.assertIn("IC transfer", payload["blockers"])
        self.assertIn("PM band-limited shear convergence", payload["blockers"])
        self.assertIn("observable chain convergence", payload["blockers"])
        self.assertIn("L_minus_to_plus", " ".join(payload["required_to_upgrade"]))
        self.assertIn("K_plus", " ".join(payload["required_to_upgrade"]))

    def test_duplicate_blockers_are_collapsed(self) -> None:
        payload = build_payload(
            lensing={
                "gates": [
                    {"gate": "Bianchi closure", "status": "open", "blocks_s8": True}
                ]
            },
            scaffolds={"tracks": [{"track": "Bianchi closure"}]},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True, "missing_survey_inputs": []},
            physical_rollup=READY_PHYSICAL_ROLLUP,
        )

        self.assertEqual(payload["blockers"].count("Bianchi closure"), 1)

    def test_controlled_pm_convergence_suppresses_numeric_blockers(self) -> None:
        payload = build_payload(
            lensing={"gates": []},
            scaffolds={"tracks": []},
            observable_chain={"blocking_issue": True},
            survey_interface={"survey_layer_ready": True, "missing_survey_inputs": []},
            pm_band_limited={"blocking_issue": True},
            pm_convergence_comparison={"controlled_numerical_convergence_ready": True},
            physical_rollup=READY_PHYSICAL_ROLLUP,
        )

        self.assertNotIn("observable chain convergence", payload["blockers"])
        self.assertNotIn("PM band-limited shear convergence", payload["blockers"])
        self.assertNotIn(
            "close grid convergence at the claimed observable resolution",
            payload["required_to_upgrade"],
        )

    def test_gate_opens_when_no_blockers_remain(self) -> None:
        payload = build_payload(
            lensing={
                "gates": [
                    {
                        "gate": "Q_det convention",
                        "status": "closed",
                        "blocks_s8": True,
                    }
                ]
            },
            scaffolds={"tracks": []},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True, "missing_survey_inputs": []},
            physical_rollup=READY_PHYSICAL_ROLLUP,
        )

        self.assertTrue(payload["prediction_ready"])
        self.assertEqual(payload["verdict"], "Prediction gate is open.")

    def test_open_physical_rollup_blocks_prediction(self) -> None:
        payload = build_payload(
            lensing={"gates": []},
            scaffolds={"tracks": []},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True, "missing_survey_inputs": []},
            physical_rollup={
                "all_terminal_blockers_closed": False,
                "physics_closed": False,
                "prediction_ready": False,
                "open_terminal_blockers": ["d_l_transport_law"],
            },
        )

        self.assertFalse(payload["prediction_ready"])
        self.assertIn("P0 d_l_transport_law", payload["blockers"])


if __name__ == "__main__":
    unittest.main()
