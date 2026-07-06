from __future__ import annotations

import unittest

from scripts.write_p0_eft_janus_z2_sigma_mpla_schwarzschild_throat_local_model import (
    build_payload,
)


class MPLASchwarzschildThroatLocalModelScriptTests(unittest.TestCase):
    def test_mpla_model_supplies_local_throat_not_absolute_scale(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["minimal_throat_ready"])
        self.assertTrue(payload["Z2_orientation_reversal_ready"])
        self.assertEqual(payload["R_Sigma_over_R_s"], 1.0)
        self.assertFalse(payload["absolute_R_Sigma_solution_ready"])
        self.assertFalse(payload["E_counterterm_derived"])
        self.assertFalse(payload["counterterm_coefficients_derived"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_s_scale_not_fixed_by_local_MPLA_throat_model",
        )

    def test_forbidden_use_is_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("absolute BAO scale closure", payload["forbidden_use"])
        self.assertIn("counterterm coefficient closure", payload["forbidden_use"])
        self.assertFalse(payload["negative_thermodynamic_density_postulated"])


if __name__ == "__main__":
    unittest.main()
