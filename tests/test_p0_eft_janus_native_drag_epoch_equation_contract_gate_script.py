import unittest

from janus_lab.janus_phase_space_occupation_search import (
    native_drag_epoch_equation_contract_payload,
)


class JanusNativeDragEpochEquationContractGateTests(unittest.TestCase):
    def test_structural_drag_equation_is_available_not_numeric(self):
        payload = native_drag_epoch_equation_contract_payload()

        self.assertTrue(payload["structural_prediction_ready"])
        self.assertFalse(payload["numeric_prediction_ready"])
        self.assertIn("x_e(a; C_ion, eta_b)", payload["equation"])

    def test_remaining_inputs_are_explicit(self):
        payload = native_drag_epoch_equation_contract_payload()

        self.assertIn("C_ion", payload["remaining_inputs"])
        self.assertIn("B_eta", payload["remaining_inputs"])
        self.assertIn("p_H_or_full_HJ", payload["remaining_inputs"])


if __name__ == "__main__":
    unittest.main()
