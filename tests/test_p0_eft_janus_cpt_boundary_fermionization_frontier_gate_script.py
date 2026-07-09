import unittest

from janus_lab.janus_phase_space_occupation_search import (
    cpt_boundary_fermionization_frontier_payload,
)


class JanusCPTBoundaryFermionizationFrontierGateTests(unittest.TestCase):
    def test_pin_spinor_inputs_exist_but_fermionization_is_missing(self):
        payload = cpt_boundary_fermionization_frontier_payload()

        self.assertTrue(payload["inputs"]["resolved_tunnel_Pin_lift_ready"])
        self.assertTrue(payload["inputs"]["Z2Sigma_spinor_projection_ready"])
        self.assertFalse(payload["requirements"]["operators_are_CAR_or_Clifford_generators"])
        self.assertFalse(payload["cpt_fermionization_derived"])

    def test_charge_conjugation_and_occupation_are_blockers(self):
        payload = cpt_boundary_fermionization_frontier_payload()
        joined = " ".join(payload["blockers"])

        self.assertIn("charge conjugation", joined)
        self.assertIn("N_occ remains open", joined)
        self.assertFalse(payload["keeps_C14_4_route_alive"])


if __name__ == "__main__":
    unittest.main()
