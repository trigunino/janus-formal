import unittest

from scripts.build_p0_eft_janus_z2_sigma_same_sector_stress_conservation_gate import (
    build_payload,
)


class SameSectorStressConservationGateTests(unittest.TestCase):
    def test_stress_conservation_layer_is_declared_but_open(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared_stress_conservation_layer_ready"])
        self.assertTrue(payload["source_derivation_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_noether_formula_is_same_sector_only(self):
        payload = build_payload()

        self.assertIn("D_plus_nu T_plus", payload["formulas"]["plus"])
        self.assertIn("D_minus_nu T_minus", payload["formulas"]["minus"])
        self.assertIn("same-sector T only", payload["formulas"]["scope"])
        self.assertTrue(payload["closure"]["cross_stress_excluded_from_same_sector_stress"])

    def test_feeds_conditional_closure_but_not_yet(self):
        payload = build_payload()
        feeds = payload["feeds_conditional_closure_gate"]

        self.assertTrue(feeds["same_sector_plus_stress_conserved"])
        self.assertTrue(feeds["same_sector_minus_stress_conserved"])
        self.assertIn("keep_cross_sector_transport_terms_separate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
