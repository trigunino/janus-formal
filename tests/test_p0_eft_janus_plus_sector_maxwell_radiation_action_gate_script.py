import unittest

from janus_lab.janus_phase_space_occupation_search import (
    plus_sector_maxwell_radiation_action_payload,
)


class JanusPlusSectorMaxwellRadiationActionGateTests(unittest.TestCase):
    def test_maxwell_action_unblocks_radiation_first_law_as_extension(self):
        payload = plus_sector_maxwell_radiation_action_payload()

        self.assertEqual(payload["action_contract"]["metric"], "g_plus")
        self.assertEqual(payload["derived_objects"]["trace"], "zero in four dimensions")
        self.assertTrue(payload["unblocks"]["adiabatic_radiation_first_law"])
        self.assertEqual(payload["paper_relation"]["classification"], "minimal_standard_extension")

    def test_paper_native_status_is_not_hidden(self):
        payload = plus_sector_maxwell_radiation_action_payload()

        self.assertFalse(payload["paper_relation"]["explicitly_given_by_paper"])
        self.assertIn("derive pre-drag H_J(a)", payload["remaining"])


if __name__ == "__main__":
    unittest.main()
