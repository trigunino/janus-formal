import unittest

from scripts.build_p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate import (
    build_payload,
)


class P0EFTJanusZ4NonlinearBoundaryVariationObligationGateTests(unittest.TestCase):
    def test_prerequisites_ready_but_nonlinear_boundary_not_closed(self):
        payload = build_payload()

        self.assertTrue(payload["nonlinear_boundary_prerequisites_ready"])
        self.assertFalse(payload["full_nonlinear_boundary_variation_closed"])
        self.assertIn(
            "nonlinear_tetrad_boundary_variation_computed",
            payload["remaining_boundary_obligations"],
        )
        self.assertIn(
            "membrane_junction_variation_computed",
            payload["remaining_boundary_obligations"],
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
