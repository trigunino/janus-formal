from __future__ import annotations

import unittest

from scripts.build_p0_projected_dust_el_cuu_derivation_chain import build_payload


class P0ProjectedDustELCuuDerivationChainTests(unittest.TestCase):
    def test_standard_projection_is_derived_but_cuu_identity_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "partial-derivation-chain-open")
        self.assertTrue(payload["standard_dust_projection_derived"])
        self.assertFalse(payload["transported_cuu_step_conditional"])
        self.assertTrue(payload["single_cross_dust_projected_cuu_identity_derived"])
        self.assertFalse(payload["projected_cuu_identity_derived"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_steps_include_variation_split_projection_and_cuu(self) -> None:
        steps = {row["step"]: row for row in build_payload()["derivation_steps"]}

        self.assertIn("el_variation", steps)
        self.assertIn("dust_divergence_split", steps)
        self.assertIn("transverse_projection", steps)
        self.assertIn("transported_acceleration_split", steps)
        self.assertIn("projected_cuu_identity", steps)
        self.assertEqual(steps["projected_cuu_identity"]["closed"], "single-cross-dust")

    def test_remaining_conditions_keep_measure_dl_mirror_and_pressure_open(self) -> None:
        conditions = " ".join(build_payload()["remaining_conditions"])

        self.assertIn("D_receiver(B_4vol rho_to u_to)=0", conditions)
        self.assertIn("dynamic phi/L", conditions)
        self.assertIn("inverse phi/L", conditions)
        self.assertIn("sign convention", conditions)
        self.assertIn("pressure/Pi", conditions)


if __name__ == "__main__":
    unittest.main()
