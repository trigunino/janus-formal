import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_exact_shape_compatibility_payload,
)


class JanusEntropyCutoffExactShapeCompatibilityGateTests(unittest.TestCase):
    def test_entropy_cutoff_requires_different_q0_on_same_shape(self):
        payload = entropy_cutoff_exact_shape_compatibility_payload()
        self.assertAlmostEqual(
            payload["entropy_cutoff_branch"]["q0_required_if_same_shape"],
            -1.0 / 2000.0,
        )
        self.assertFalse(payload["same_branch_compatible"])

    def test_late_branch_is_preserved_as_separate_requirement(self):
        payload = entropy_cutoff_exact_shape_compatibility_payload()
        self.assertAlmostEqual(payload["published_late_SN_branch"]["q0"], -0.087)
        self.assertIn("early-to-late matching", " ".join(payload["next_required"]))


if __name__ == "__main__":
    unittest.main()
