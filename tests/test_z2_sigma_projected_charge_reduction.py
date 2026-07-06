import unittest

from src.janus_lab.z2_sigma_projected_charge_reduction import (
    occupation_degeneracy_payload,
    reduce_deck_invariant_projected_charge,
    z2_projected_charge_reduction_payload,
)


class Z2SigmaProjectedChargeReductionTest(unittest.TestCase):
    def test_z2_reduces_projection_to_single_occupation_datum(self):
        payload = z2_projected_charge_reduction_payload()

        self.assertFalse(payload["projection_weights_free"])
        self.assertEqual(payload["projection_weights"], {"N_plus": 0.5, "N_minus": 0.5})
        self.assertEqual(
            payload["deck_invariant_sector"]["projected_charge_formula"],
            "N_Z2Sigma = N_occ",
        )
        self.assertFalse(payload["deck_invariant_sector"]["absolute_N_occ_fixed"])
        self.assertEqual(payload["remaining_open_data"], ["N_occ"])

    def test_deck_invariant_reduction_keeps_occupation_value(self):
        self.assertEqual(reduce_deck_invariant_projected_charge(3.0), 3.0)
        with self.assertRaisesRegex(ValueError, "occupation"):
            reduce_deck_invariant_projected_charge(0.0)

    def test_noether_constraints_leave_occupation_degenerate(self):
        payload = occupation_degeneracy_payload([1.0, 2.0])

        self.assertEqual(payload["projected_charges"], [1.0, 2.0])
        self.assertTrue(payload["all_satisfy_Z2_deck_invariant_constraint"])
        self.assertFalse(payload["topology_selects_unique_occupation"])
        self.assertFalse(payload["charge_conservation_selects_unique_occupation"])


if __name__ == "__main__":
    unittest.main()
