import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    exotic_pt_transition_configuration_matrix_payload,
)


class JanusExoticPTTransitionConfigurationMatrixGateTests(unittest.TestCase):
    def test_weyl_cusp_is_ranked_first(self):
        payload = exotic_pt_transition_configuration_matrix_payload()
        self.assertEqual(payload["recommended_next"], "WeylCuspPTBoundary")
        self.assertEqual(payload["candidates"][0]["name"], "WeylCuspPTBoundary")

    def test_mobius_kept_as_speculative_candidate(self):
        payload = exotic_pt_transition_configuration_matrix_payload()
        names = {row["name"] for row in payload["candidates"]}
        self.assertIn("MobiusNormalBand", names)


if __name__ == "__main__":
    unittest.main()
