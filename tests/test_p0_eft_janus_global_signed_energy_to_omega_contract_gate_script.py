import unittest

from src.janus_lab.janus_phase_space_occupation_search import global_signed_energy_to_omega_contract_payload


class JanusGlobalSignedEnergyToOmegaContractGateTests(unittest.TestCase):
    def test_conservation_gives_relation_not_value(self):
        payload = global_signed_energy_to_omega_contract_payload()
        self.assertTrue(payload["algebraic_contract_closed"])
        self.assertFalse(payload["omega_fixed_by_conservation"])
        self.assertIn("Omega^3", payload["omega_relation"])


if __name__ == "__main__":
    unittest.main()
