import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    weyl_cusp_physical_clock_candidate_matrix_payload,
)


class JanusWeylCuspPhysicalClockCandidateMatrixGateTests(unittest.TestCase):
    def test_visible_matter_frame_ranked_first(self):
        payload = weyl_cusp_physical_clock_candidate_matrix_payload()
        self.assertEqual(payload["recommended_next"], "VisibleMatterJordanFrame")
        self.assertEqual(payload["candidates"][0]["name"], "VisibleMatterJordanFrame")

    def test_pure_conformal_geometry_rejected(self):
        payload = weyl_cusp_physical_clock_candidate_matrix_payload()
        self.assertEqual(payload["rejected_as_pure_geometry"], "PureConformalGeometryClock")


if __name__ == "__main__":
    unittest.main()
