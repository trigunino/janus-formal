import unittest

from scripts.build_p0_eft_janus_z2_sigma_abstract_tensor_transport_bianchi_gate import (
    build_payload,
)


class AbstractTensorTransportBianchiGateTests(unittest.TestCase):
    def test_formal_bianchi_implication_is_closed_but_source_open(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["route_status"], "formal_conditional_closed_source_open")
        self.assertTrue(payload["formal_bianchi_closed"])
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["conditions_source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(payload["primary_blocker"], "source_derivation_of_transport_maps")

    def test_maps_and_rhs_are_declared_both_ways(self):
        payload = build_payload()
        definitions = payload["definitions"]
        closure = payload["closure"]

        self.assertIn("Transport_{- to +}", definitions["K_plus"])
        self.assertIn("Transport_{+ to -}", definitions["K_minus"])
        self.assertIn("B_plus K_plus", definitions["S_plus"])
        self.assertIn("B_minus K_minus", definitions["S_minus"])
        self.assertTrue(closure["plus_Bianchi_residual_vanishes_formally"])
        self.assertTrue(closure["minus_Bianchi_residual_vanishes_formally"])

    def test_shortcuts_remain_forbidden(self):
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])
        next_required = " ".join(payload["next_required"])

        self.assertIn("untransported tensor copy", forbidden)
        self.assertIn("Q_cross", forbidden)
        self.assertIn("derive_M_minus_to_plus", next_required)
        self.assertIn("reuse_same_bridge", next_required)


if __name__ == "__main__":
    unittest.main()
