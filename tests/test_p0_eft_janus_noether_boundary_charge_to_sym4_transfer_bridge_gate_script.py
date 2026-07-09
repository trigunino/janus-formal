import unittest

from janus_lab.janus_phase_space_occupation_search import (
    noether_boundary_charge_to_sym4_transfer_bridge_payload,
)


class JanusNoetherBoundaryChargeToSym4TransferBridgeGateTests(unittest.TestCase):
    def test_reuses_symbolic_noether_boundary_charge_only(self):
        payload = noether_boundary_charge_to_sym4_transfer_bridge_payload()
        existing = payload["existing_z2_sigma_boundary_charge"]

        self.assertTrue(existing["symbolic_boundary_hamiltonian_ready"])
        self.assertFalse(existing["numeric_boundary_hamiltonian_ready"])
        self.assertIn("absolute_surface_measure_available", existing["blocked_by"])

    def test_bridge_to_sym4_is_not_closed(self):
        payload = noether_boundary_charge_to_sym4_transfer_bridge_payload()

        self.assertFalse(payload["sym4_transfer_bridge_requirements"]["map_boundary_H_to_End_Sym4C11"])
        self.assertFalse(payload["sym4_transfer_bridge_requirements"]["prove_ordered_1001_spectrum"])
        self.assertEqual(payload["if_bridge_closes"]["z_max"], 1000.0)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
