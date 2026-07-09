import unittest

from janus_lab.janus_phase_space_occupation_search import (
    boundary_hamiltonian_scalar_vs_operator_audit_payload,
)


class JanusBoundaryHamiltonianScalarVsOperatorAuditGateTests(unittest.TestCase):
    def test_scalar_boundary_energy_cannot_order_sym4(self):
        payload = boundary_hamiltonian_scalar_vs_operator_audit_payload()
        cases = {row["case"]: row for row in payload["cases"]}

        self.assertEqual(payload["inputs"]["Hilbert_dimension"], 1001)
        self.assertFalse(payload["scalar_boundary_H_orders_states"])
        self.assertFalse(cases["scalar_boundary_energy"]["orders_1001_states"])

    def test_operator_boundary_hamiltonian_is_missing(self):
        payload = boundary_hamiltonian_scalar_vs_operator_audit_payload()

        self.assertFalse(payload["operator_valued_boundary_H_available"])
        self.assertEqual(payload["if_operator_requirement_closes"]["z_max"], 1000.0)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
