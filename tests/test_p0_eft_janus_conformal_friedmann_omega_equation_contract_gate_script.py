import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    conformal_friedmann_omega_equation_contract_payload,
)


class JanusConformalFriedmannOmegaEquationContractGateTests(unittest.TestCase):
    def test_equation_contract_closed_but_solution_open(self):
        payload = conformal_friedmann_omega_equation_contract_payload()
        self.assertTrue(payload["equation_contract_closed"])
        self.assertFalse(payload["omega_solution_closed"])
        self.assertIn("d ln(Omega)", payload["equation_contract"]["omega_equation"])


if __name__ == "__main__":
    unittest.main()
