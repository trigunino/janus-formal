import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_real_state_materialization_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaBAORealStateMaterializationGateTests(unittest.TestCase):
    def test_missing_real_inputs_keep_gate_red(self):
        payload = build_payload(
            physical_payload={
                "status": "physical",
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "uses_compressed_planck_lcdm": False,
                "uses_archived_z4": False,
                "nearest_physical_inputs_frontier": {
                    "blocks": ["active_FLRW_component_manifest"]
                },
                "blocker": "missing active FLRW component manifest",
            }
        )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["real_active_inputs_missing"])
        self.assertTrue(payload["fixture_result_is_not_physical_result"])
        self.assertIn("active_FLRW_component_manifest", payload["missing_real_active_inputs"])

    def test_complete_real_state_can_pass(self):
        payload = build_payload(
            physical_payload={
                "status": "physical",
                "gate_passed": True,
                "bao_chi2_evaluated": True,
                "chi2_DESI_DR2_BAO": 12.5,
                "prediction_vector": [1.0] * 13,
                "uses_compressed_planck_lcdm": False,
                "uses_archived_z4": False,
                "uses_observational_H0_fit": False,
                "uses_observational_curvature_fit": False,
                "nearest_physical_inputs_frontier": {"blocks": []},
                "blocker": None,
            }
        )

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["real_active_inputs_missing"])
        self.assertFalse(payload["fixture_result_is_not_physical_result"])
        self.assertEqual(payload["prediction_vector_length"], 13)


if __name__ == "__main__":
    unittest.main()
