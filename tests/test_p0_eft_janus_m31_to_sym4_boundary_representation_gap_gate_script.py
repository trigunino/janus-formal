import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_to_sym4_boundary_representation_gap_payload,
)


class JanusM31ToSym4BoundaryRepresentationGapGateTests(unittest.TestCase):
    def test_m31_anchor_is_available_but_boundary_representation_is_not(self):
        payload = m31_to_sym4_boundary_representation_gap_payload()

        self.assertIn("M31 coadjoint/torsor action available", payload["closed_steps"])
        self.assertIn("identify boundary mode space V with C^11", payload["closed_steps"])
        self.assertIn("derive rho: janus_lie -> End(V)", payload["open_steps"])

    def test_if_closed_it_reaches_predrag(self):
        payload = m31_to_sym4_boundary_representation_gap_payload()

        self.assertEqual(payload["inputs"]["target_dimension"], 1001)
        self.assertEqual(payload["if_closed"]["z_max"], 1000.0)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
