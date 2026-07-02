import unittest

from scripts.build_p0_eft_janus_z4_nonlinear_el_residual_obligation_gate import (
    build_payload,
)


class P0EFTJanusZ4NonlinearELResidualObligationGateTests(unittest.TestCase):
    def test_el_residual_reduced_but_common_obstruction_open(self):
        payload = build_payload()

        self.assertTrue(payload["nonlinear_el_residual_reduced_to_common_obstruction"])
        self.assertEqual(payload["common_obstruction"], "O_nl")
        self.assertFalse(payload["nonlinear_el_residual_closed"])
        self.assertIn(
            "common_obstruction_vanishes",
            payload["remaining_el_obligations"],
        )
        self.assertIn(
            "nonlinear_euler_lagrange_residual_vanishing",
            payload["remaining_el_obligations"],
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
