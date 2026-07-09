import unittest

from janus_lab.janus_phase_space_occupation_search import (
    plus_sector_photon_stress_conservation_payload,
)


class JanusPlusSectorPhotonStressConservationGateTests(unittest.TestCase):
    def test_noether_route_is_conditionally_available(self):
        payload = plus_sector_photon_stress_conservation_payload()

        self.assertTrue(payload["anchors"]["M15_positive_photons_follow_g_plus"])
        self.assertTrue(payload["anchors"]["M30_distinct_geodesic_families"])
        self.assertTrue(
            payload["plus_sector_photon_stress_conservation_conditionally_derived"]
        )
        self.assertTrue(
            payload[
                "plus_sector_photon_stress_conservation_unconditionally_derived_within_extension"
            ]
        )
        self.assertFalse(payload["plus_sector_photon_stress_conservation_paper_native"])

    def test_missing_photon_action_is_explicit(self):
        payload = plus_sector_photon_stress_conservation_payload()

        self.assertTrue(payload["required_action_inputs"]["plus_sector_photon_action_declared"])
        self.assertFalse(payload["required_action_inputs"]["paper_native_explicit_formula"])
        self.assertIn(
            "decide whether standard Maxwell completion is accepted as model extension or kept as paper-external",
            payload["remaining_non_rustine_proof_obligations"],
        )


if __name__ == "__main__":
    unittest.main()
