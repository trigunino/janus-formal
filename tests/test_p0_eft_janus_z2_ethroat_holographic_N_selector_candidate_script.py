import unittest

from scripts.build_p0_eft_janus_z2_ethroat_holographic_N_selector_candidate import (
    build_payload,
)


class EThroatHolographicNSelectorCandidateTests(unittest.TestCase):
    def test_required_N_is_macroscopic(self):
        payload = build_payload()
        n = payload["required_N_cases"]["published_janus_q0"]["N_required"]

        self.assertGreater(n, 1.0e119)
        self.assertLess(n, 1.0e122)

    def test_horizon_routes_are_circular_for_H0_prediction(self):
        payload = build_payload()

        self.assertTrue(payload["candidate_routes"]["cosmological_horizon_entropy"]["gets_10_120"])
        self.assertFalse(
            payload["candidate_routes"]["cosmological_horizon_entropy"][
                "selects_N_without_H0"
            ]
        )
        self.assertFalse(payload["non_circular_selector_found"])

    def test_primitive_sector_is_non_circular_but_wrong_scale(self):
        route = build_payload()["candidate_routes"]["primitive_topological_sector"]

        self.assertTrue(route["selects_N_without_H0"])
        self.assertFalse(route["gets_10_120"])


if __name__ == "__main__":
    unittest.main()
