from __future__ import annotations

import unittest

from src.janus_lab.mpla_schwarzschild_throat import (
    mpla_areal_radius,
    mpla_areal_radius_prime,
    mpla_areal_radius_second,
    mpla_throat_certificate,
)


class MPLASchwarzschildThroatTests(unittest.TestCase):
    def test_throat_is_minimal_and_even(self) -> None:
        cert = mpla_throat_certificate(rs=2.0)

        self.assertEqual(cert["R_Sigma"], 2.0)
        self.assertEqual(cert["R_prime_at_Sigma"], 0.0)
        self.assertEqual(cert["R_second_at_Sigma"], 2.0)
        self.assertTrue(cert["minimal_throat"])
        self.assertTrue(cert["Z2_rho_reflection_even_radius"])
        self.assertFalse(cert["absolute_scale_fixed_by_model"])

    def test_radius_is_even_under_rho_reflection(self) -> None:
        for rho in [0.1, 0.5, 1.0]:
            self.assertAlmostEqual(mpla_areal_radius(rho), mpla_areal_radius(-rho))
            self.assertAlmostEqual(
                mpla_areal_radius_prime(rho),
                -mpla_areal_radius_prime(-rho),
            )
            self.assertAlmostEqual(
                mpla_areal_radius_second(rho),
                mpla_areal_radius_second(-rho),
            )


if __name__ == "__main__":
    unittest.main()
