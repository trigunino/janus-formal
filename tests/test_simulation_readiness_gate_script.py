from __future__ import annotations

import unittest

from scripts.build_simulation_readiness_gate import build_payload


class SimulationReadinessGateTests(unittest.TestCase):
    def test_blocks_full_simulation_when_math_or_survey_is_open(self) -> None:
        payload = build_payload(
            prediction_gate={"blockers": ["Bianchi closure", "Q_cross"]},
            scaffolds={
                "tracks": [
                    {"track": "Bianchi closure", "parallelizable": True},
                    {"track": "Survey layer", "parallelizable": False},
                ]
            },
            pm_convergence={"controlled_numerical_convergence_ready": True},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": False},
            partial_artifacts=[
                {
                    "description": "Bounded Lorentz-boost branch",
                    "status": "bounded-derivation-branch",
                    "physics_closed": False,
                    "prediction_ready": False,
                }
            ],
            grids=[8, 16],
        )

        self.assertFalse(payload["full_cosmological_simulation_ready"])
        self.assertEqual(payload["allowed_execution_level"], "diagnostic_pm_only")
        self.assertIn("Q_det and Q_cross remain separate", " ".join(payload["no_rustine_policy"]))
        self.assertIn("Bianchi closure", payload["parallel_tracks"])
        self.assertEqual(payload["partial_closures"][0]["status"], "bounded-derivation-branch")
        self.assertFalse(payload["partial_artifacts_ready"])
        self.assertEqual(len(payload["open_partial_closures"]), 1)

    def test_resource_budget_uses_two_sector_particle_count(self) -> None:
        payload = build_payload(
            prediction_gate={"blockers": []},
            scaffolds={"tracks": []},
            pm_convergence={"controlled_numerical_convergence_ready": True},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True},
            partial_artifacts=[
                {
                    "description": "Closed physical rollup",
                    "status": "closed",
                    "physics_closed": True,
                    "prediction_ready": True,
                }
            ],
            grids=[4],
        )

        self.assertTrue(payload["full_cosmological_simulation_ready"])
        self.assertEqual(payload["resource_budget"][0]["particle_count"], 2 * 4**3)
        self.assertGreater(payload["resource_budget"][0]["estimated_core_memory_gb"], 0.0)
        self.assertFalse(payload["missing_partial_artifacts"])

    def test_open_partial_ledger_blocks_candidate_pipeline(self) -> None:
        payload = build_payload(
            prediction_gate={"blockers": []},
            scaffolds={"tracks": []},
            pm_convergence={"controlled_numerical_convergence_ready": True},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True},
            partial_artifacts=[
                {
                    "description": "P0 source residual closure matrix",
                    "status": "source-residual-closure-obligation-matrix-open",
                    "physics_closed": False,
                    "prediction_ready": False,
                }
            ],
            grids=[4],
        )

        self.assertFalse(payload["full_cosmological_simulation_ready"])
        self.assertEqual(payload["allowed_execution_level"], "diagnostic_pm_only")
        self.assertFalse(payload["partial_artifacts_ready"])
        self.assertEqual(payload["open_partial_closures"][0]["status"], "source-residual-closure-obligation-matrix-open")

    def test_missing_partial_rollup_blocks_candidate_pipeline(self) -> None:
        payload = build_payload(
            prediction_gate={"blockers": []},
            scaffolds={"tracks": []},
            pm_convergence={"controlled_numerical_convergence_ready": True},
            observable_chain={"blocking_issue": False},
            survey_interface={"survey_layer_ready": True},
            grids=[4],
        )

        self.assertFalse(payload["full_cosmological_simulation_ready"])
        self.assertTrue(payload["missing_partial_artifacts"])
        self.assertFalse(payload["partial_artifacts_ready"])


if __name__ == "__main__":
    unittest.main()
