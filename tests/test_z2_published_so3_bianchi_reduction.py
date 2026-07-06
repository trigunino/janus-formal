from __future__ import annotations

import unittest

from src.janus_lab.z2_published_so3_bianchi_reduction import (
    published_so3_bianchi_reduction_payload,
)


class PublishedSO3BianchiReductionTests(unittest.TestCase):
    def test_so3_reduction_is_asymptotic_not_generic(self) -> None:
        payload = published_so3_bianchi_reduction_payload()

        self.assertTrue(payload["stationary_so3_reduced_bianchi_ready"])
        self.assertTrue(payload["tov_newtonian_bianchi_asymptotic_ready"])
        self.assertFalse(payload["generic_tensor_bianchi_ready"])
        self.assertFalse(payload["sigma_transport_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_sign_dynamics_are_declared(self) -> None:
        terms = published_so3_bianchi_reduction_payload()["interaction_terms"]

        self.assertEqual(terms["positive_source_positive_test"]["force_sign"], "attractive")
        self.assertEqual(terms["negative_source_negative_test"]["force_sign"], "attractive")
        self.assertEqual(terms["positive_source_negative_test"]["force_sign"], "repulsive")
        self.assertEqual(terms["negative_source_positive_test"]["force_sign"], "repulsive")


if __name__ == "__main__":
    unittest.main()
