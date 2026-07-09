import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    souriau_torsor_c11_no_carry_bridge_payload,
)


class JanusSouriauTorsorC11NoCarryBridgeGateTests(unittest.TestCase):
    def test_torsor_components_sum_to_c11(self):
        payload = souriau_torsor_c11_no_carry_bridge_payload()
        self.assertTrue(payload["C11_basis_identified"])
        self.assertEqual(sum(row["dimension"] for row in payload["components"]), 11)

    def test_ordering_remains_unproved(self):
        payload = souriau_torsor_c11_no_carry_bridge_payload()
        self.assertFalse(payload["canonical_component_order_derived"])
        self.assertTrue(payload["what_remains_unproved"]["ordered_component_chain_from_Janus_group_action"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
