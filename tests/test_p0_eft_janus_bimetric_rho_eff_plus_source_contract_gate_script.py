import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    janus_bimetric_rho_eff_plus_source_contract_payload,
)


class JanusBimetricRhoEffPlusSourceContractGateTests(unittest.TestCase):
    def test_contract_closed_but_predrag_open(self):
        payload = janus_bimetric_rho_eff_plus_source_contract_payload()
        self.assertTrue(payload["source_contract_closed"])
        self.assertFalse(payload["active_predrag_source_closed"])
        self.assertIn("Q_det", payload["contract"])


if __name__ == "__main__":
    unittest.main()
