import unittest

from janus_lab.janus_phase_space_occupation_search import (
    pt_normal_to_sym4_internal_matrix_attempt_payload,
)


class JanusPTNormalToSym4InternalMatrixAttemptGateTests(unittest.TestCase):
    def test_pt_signs_and_leg_exchange_do_not_order_sym4(self):
        payload = pt_normal_to_sym4_internal_matrix_attempt_payload()
        rows = {row["action"]: row for row in payload["tested_actions"]}

        self.assertFalse(rows["global_PT_sign_on_all_modes"]["orders_1001_states"])
        self.assertFalse(rows["plus_minus_leg_exchange"]["orders_1001_states"])
        self.assertFalse(payload["derived_non_scalar_internal_matrix_now"])

    def test_normal_connection_endomorphism_is_remaining_object(self):
        payload = pt_normal_to_sym4_internal_matrix_attempt_payload()

        self.assertEqual(payload["best_remaining_object"], "normal_connection_endomorphism_A_normal_on_C11")
        self.assertFalse(payload["A_normal_requirements"]["normal_connection_on_mode_bundle_derived"])
        self.assertEqual(payload["if_A_normal_closes"]["z_max"], 1000.0)


if __name__ == "__main__":
    unittest.main()
