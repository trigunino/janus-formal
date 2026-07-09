import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    microcanonical_boundary_state_law_attempt_payload,
)


class JanusMicrocanonicalBoundaryStateLawAttemptGateTests(unittest.TestCase):
    def test_microcanonical_state_is_isotropic_and_counts_1001(self):
        payload = microcanonical_boundary_state_law_attempt_payload()
        self.assertTrue(payload["symmetry"]["SO3_invariant"])
        self.assertFalse(payload["symmetry"]["selects_visible_xyz_direction"])
        self.assertEqual(payload["entropy"]["dim_H_boundary"], 1001)

    def test_entropy_ruler_map_is_not_claimed_as_derived(self):
        payload = microcanonical_boundary_state_law_attempt_payload()
        self.assertTrue(payload["ruler_map_attempt"]["pre_drag_reach"])
        self.assertFalse(payload["ruler_map_attempt"]["derives_ruler_from_entropy"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
