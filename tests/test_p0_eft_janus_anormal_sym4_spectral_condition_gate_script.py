import unittest

from janus_lab.janus_phase_space_occupation_search import (
    anormal_sym4_spectral_condition_payload,
)


class JanusAnormalSym4SpectralConditionGateTests(unittest.TestCase):
    def test_block_and_arithmetic_weights_do_not_order_1001(self):
        payload = anormal_sym4_spectral_condition_payload()
        cases = {row["name"]: row for row in payload["cases"]}

        self.assertEqual(payload["target"]["Sym4_dimension"], 1001)
        self.assertEqual(cases["M31_block_profile_weights"]["distinct_levels"], 70)
        self.assertFalse(cases["M31_block_profile_weights"]["orders_1001"])
        self.assertFalse(cases["arithmetic_component_weights_0_to_10"]["orders_1001"])

    def test_dissociated_weights_work_but_are_not_janus_anchored(self):
        payload = anormal_sym4_spectral_condition_payload()
        cases = {row["name"]: row for row in payload["cases"]}

        self.assertEqual(cases["base5_dissociated_weights"]["distinct_levels"], 1001)
        self.assertTrue(cases["base5_dissociated_weights"]["orders_1001"])
        self.assertFalse(cases["base5_dissociated_weights"]["janus_anchored"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
