import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    anormal_weight_origin_candidate_matrix_payload,
)


class JanusANormalWeightOriginCandidateMatrixGateTests(unittest.TestCase):
    def test_rejects_known_non_closures(self):
        payload = anormal_weight_origin_candidate_matrix_payload()
        rejected = set(payload["rejected_as_no_fit_closures"])
        self.assertIn("scalar_quasilocal_boundary_charge", rejected)
        self.assertIn("published_M31_block_weights", rejected)
        self.assertIn("generic_base5_weight_law", rejected)

    def test_keeps_only_physical_remaining_routes(self):
        payload = anormal_weight_origin_candidate_matrix_payload()
        self.assertEqual(
            payload["credible_remaining_routes"],
            ["active_PT_Sigma_normal_connection", "boundary_modular_state"],
        )
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
