import unittest

from janus_lab.janus_phase_space_occupation_search import (
    native_drag_exponent_frontier_payload,
)


class JanusNativeDragExponentFrontierGateTests(unittest.TestCase):
    def test_drag_exponent_and_required_h_regime(self):
        payload = native_drag_exponent_frontier_payload()

        self.assertEqual(payload["derived_exponents"]["Gamma_drag"], -1.5)
        self.assertEqual(payload["condition_for_standard_early_coupling"]["required"], "p > -3/2")

    def test_radiation_like_h_is_not_enough(self):
        payload = native_drag_exponent_frontier_payload()
        rows = {row["name"]: row for row in payload["candidate_H_scalings"]}

        self.assertFalse(rows["standard_radiation_like"]["early_coupling_stronger"])
        self.assertFalse(rows["variable_G_radiation_like"]["early_coupling_stronger"])
        self.assertTrue(rows["constant_H_bridge_like"]["early_coupling_stronger"])


if __name__ == "__main__":
    unittest.main()
