import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_sym4_boundary_state_law_derivation_attempt_payload,
)


class JanusM31Sym4BoundaryStateLawDerivationAttemptGateTests(unittest.TestCase):
    def test_sym4_closes_number_but_not_state_law(self):
        payload = m31_sym4_boundary_state_law_derivation_attempt_payload()

        self.assertEqual(payload["candidate"], "Sym^4(C^11)")
        self.assertEqual(payload["required_N"], 1001)
        self.assertFalse(payload["no_fit_closed_now"])
        self.assertIn("M31 supplies an 11-dimensional Janus Lie/torsor vector space V", payload["closed_steps"])

    def test_accepting_open_steps_would_reach_predrag(self):
        payload = m31_sym4_boundary_state_law_derivation_attempt_payload()
        accepted = payload["if_last_two_steps_are_accepted"]

        self.assertEqual(accepted["N_selected"], 1001)
        self.assertAlmostEqual(accepted["a_min"], 1.0 / 1001.0)
        self.assertEqual(accepted["geometric_z_max"], 1000.0)
        self.assertTrue(accepted["pre_drag_reach"])
        self.assertIn("why dim(Sym^4) sets a_min", payload["bottom_line"])


if __name__ == "__main__":
    unittest.main()
