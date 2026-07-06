import unittest

from janus_lab.z2_sigma_round_throat_counterterm import (
    RoundThroatCountertermCoefficients,
    no_extension_zero_source_constraints,
    positive_round_throat_radius_roots,
    round_throat_e_counterterm_values,
    round_throat_lct_values,
)


class RoundThroatCountertermTests(unittest.TestCase):
    def test_lct_and_e_counterterm_formula(self):
        coeff = RoundThroatCountertermCoefficients(
            a0=1.0,
            a1=2.0,
            a2=3.0,
            a3=4.0,
            epsilon_z2=-1.0,
            sqrt_det_q=2.0,
        )

        self.assertEqual(round_throat_lct_values([2.0], coeff).tolist(), [1.0 - 3.0 + 9.75])
        self.assertEqual(
            round_throat_e_counterterm_values([2.0], coeff).tolist(),
            [2.0 * (12.0 - 24.0 + 27.0 + 12.0)],
        )

    def test_positive_round_throat_radius_roots(self):
        coeff = RoundThroatCountertermCoefficients(
            a0=1.0,
            a1=0.0,
            a2=-1.0,
            a3=0.0,
            epsilon_z2=1.0,
        )

        self.assertEqual(positive_round_throat_radius_roots(coeff=coeff), [1.732050807568877])

    def test_no_extension_zero_source_constraints_do_not_select_radius(self):
        constraints = no_extension_zero_source_constraints()

        self.assertEqual(
            constraints["zero_for_all_positive_R_constraints"],
            {"a0": "0", "a1": "0", "a3": "-3*a2"},
        )
        self.assertFalse(constraints["radius_selected"])
        self.assertEqual(constraints["counterterm_density_on_round_throat"], "0")


if __name__ == "__main__":
    unittest.main()
