import unittest

from scripts.build_p0_eft_janus_z4_master_membrane_transport_regularization_gate import build_payload


class P0EFTJanusZ4MasterMembraneTransportRegularizationGateTests(unittest.TestCase):
    def test_membrane_transport_regularization_is_derived_but_not_planck_unlock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-membrane-transport-regularization-gate")
        self.assertTrue(payload["shape_regularization_gate_passed"])
        self.assertTrue(payload["transport_solution_verified"])
        self.assertTrue(payload["response_bounded"])
        self.assertTrue(payload["response_monotone"])
        self.assertTrue(payload["response_odd"])
        self.assertTrue(payload["membrane_transport_derived"])
        self.assertFalse(payload["full_upstream_action_derived"])
        self.assertLess(payload["carrier_parallel_fraction_after_regularization"], 0.7)
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
