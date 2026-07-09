import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    crosscap_pt_transition_obstruction_payload,
)


class JanusCrosscapPTTransitionObstructionGateTests(unittest.TestCase):
    def test_crosscap_has_topology_but_no_local_dynamics(self):
        payload = crosscap_pt_transition_obstruction_payload()
        self.assertTrue(payload["checks"]["topological_z2_action_available"])
        self.assertFalse(payload["checks"]["local_field_equations_on_crosscap_derived"])
        self.assertFalse(payload["closed_now"])


if __name__ == "__main__":
    unittest.main()
