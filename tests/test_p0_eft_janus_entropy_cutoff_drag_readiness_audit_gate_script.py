import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_drag_readiness_audit_payload,
)


class JanusEntropyCutoffDragReadinessAuditGateTests(unittest.TestCase):
    def test_cion_and_photon_inputs_are_available(self):
        payload = entropy_cutoff_drag_readiness_audit_payload()
        self.assertTrue(payload["entropy_cutoff_available"])
        self.assertIsNotNone(payload["C_ion_from_CODATA_FIRAS"])
        self.assertTrue(payload["closed_or_conditionally_closed"]["photon_density_normalization"])

    def test_drag_is_still_not_executable(self):
        payload = entropy_cutoff_drag_readiness_audit_payload()
        self.assertTrue(payload["still_missing_for_drag_epoch"]["baryon_number_or_eta_b_normalization"])
        self.assertTrue(payload["still_missing_for_drag_epoch"]["native_H_J_of_a"])
        self.assertFalse(payload["drag_prediction_executable"])


if __name__ == "__main__":
    unittest.main()
