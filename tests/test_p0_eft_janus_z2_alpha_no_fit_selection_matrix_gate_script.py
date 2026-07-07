import unittest

from scripts.build_p0_eft_janus_z2_alpha_no_fit_selection_matrix_gate import build_payload


class AlphaNoFitSelectionMatrixGateTests(unittest.TestCase):
    def test_matrix_contains_expected_routes(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["route_count"], 12)
        self.assertIn(11, payload["open_or_conditional_route_ids"])
        self.assertIn(1, payload["potential_no_fit_route_ids"])

    def test_observational_route_is_not_no_fit(self):
        payload = build_payload()
        observational = next(r for r in payload["routes"] if r["id"] == 9)
        moebius = next(r for r in payload["routes"] if r["id"] == 11)

        self.assertFalse(observational["no_fit_if_closed"])
        self.assertEqual(moebius["status"], "new_candidate")
        self.assertIn("4D_lift", moebius["hard_blocker"])


if __name__ == "__main__":
    unittest.main()
