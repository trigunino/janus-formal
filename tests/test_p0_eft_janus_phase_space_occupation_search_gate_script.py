import unittest

from janus_lab.janus_phase_space_occupation_search import occupation_search_payload


class JanusPhaseSpaceOccupationSearchGateTests(unittest.TestCase):
    def test_search_finds_required_exponent_candidates(self):
        payload = occupation_search_payload()

        self.assertEqual(payload["required_occupation_exponent"], 3.0)
        self.assertIn("adiabatic_radiation_first_law", payload["matching_exponent_candidates"])
        self.assertIn("sigma_volume_modes", payload["matching_exponent_candidates"])
        self.assertIn("horizon_volume_modes", payload["matching_exponent_candidates"])

    def test_constant_topology_and_h3_cell_are_rejected(self):
        candidates = {item["name"]: item for item in occupation_search_payload()["candidates"]}

        self.assertEqual(candidates["z2_sheet_multiplicity"]["status"], "rejected")
        self.assertEqual(candidates["quantum_cell_h3_deformation"]["status"], "rejected")
        self.assertFalse(candidates["sigma_area_modes"]["matches_required_exponent"])

    def test_best_candidate_is_conditional_not_promoted(self):
        payload = occupation_search_payload()
        candidates = {item["name"]: item for item in payload["candidates"]}

        self.assertEqual(payload["best_current_candidate"], "adiabatic_radiation_first_law")
        self.assertEqual(candidates["adiabatic_radiation_first_law"]["status"], "conditional_candidate")
        self.assertIn("derive the radiation first law", candidates["adiabatic_radiation_first_law"]["next_required"])


if __name__ == "__main__":
    unittest.main()
