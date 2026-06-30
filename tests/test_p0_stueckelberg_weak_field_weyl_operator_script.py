from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_weak_field_weyl_operator import build_payload


class P0StueckelbergWeakFieldWeylOperatorTests(unittest.TestCase):
    def test_operator_is_available_but_not_predictive(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["weak_field_weyl_operator_available"])
        self.assertTrue(decision["weyl_trace_free_output_available"])
        self.assertFalse(decision["metric_potential_source_derived"])
        self.assertFalse(decision["full_tensor_weyl_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_operator_separates_convergence_and_weyl_shear(self) -> None:
        operator = build_payload()["operator"]

        self.assertIn("partial_xx + partial_yy", operator["convergence"])
        self.assertIn("partial_xx - partial_yy", operator["weyl_gamma1"])
        self.assertIn("partial_xy", operator["weyl_gamma2"])

    def test_obligations_forbid_hidden_fits_and_absorption(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("not from survey shear", obligations)
        self.assertIn("separate outputs", obligations)
        self.assertIn("forbid Q_cross or Q_det absorption", obligations)
        self.assertIn("affine normalization", obligations)


if __name__ == "__main__":
    unittest.main()
