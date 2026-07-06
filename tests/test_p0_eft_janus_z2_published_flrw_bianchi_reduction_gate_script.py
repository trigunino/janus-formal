from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_published_flrw_bianchi_reduction_gate import (
    build_payload,
)


class PublishedFLRWBianchiReductionGateTests(unittest.TestCase):
    def test_flrw_dust_sector_closes_but_not_generic_tensor(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["interaction_slots_ready"])
        self.assertTrue(payload["determinant_formula_closed"])
        self.assertTrue(payload["dust_scalar_transport_closed"])
        self.assertTrue(payload["flrw_reduced_bianchi_ready"])
        self.assertFalse(payload["generic_tensor_bianchi_ready"])
        self.assertFalse(payload["sigma_transport_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_non_claims_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("not generic nonlinear interaction tensor", payload["non_claims"])
        self.assertIn("not surface counterterm closure", payload["non_claims"])
        self.assertIn("not Sigma junction source", payload["non_claims"])


if __name__ == "__main__":
    unittest.main()
