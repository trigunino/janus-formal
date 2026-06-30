from __future__ import annotations

import unittest

from scripts.build_p0_eft_radion_potential_derivation import build_payload, derive_potential


class P0EFTRadionPotentialDerivationTests(unittest.TestCase):
    def test_even_volume_branch_derives_cosh_shape(self) -> None:
        derivation = derive_potential()

        self.assertTrue(derivation["matches_cosh"])
        self.assertEqual(derivation["normalized_potential"], "Lambda_J*(cosh(chi*gamma) - 1)")

    def test_minimal_ec_alone_does_not_generate_potential(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["minimal_EC_derivative_torsion_generates_bulk_potential"])
        self.assertTrue(status["janus_volume_holonomy_generates_even_potential"])

    def test_amplitude_remains_explicit_lock(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["amplitude_fixed_by_dS_residual"])
        self.assertFalse(status["potential_fully_fixed_no_fit"])

    def test_canonical_gamma_is_recorded(self) -> None:
        branch = build_payload()["janus_volume_branch"]

        self.assertEqual(branch["canonical_gamma"], "1/sqrt(6)")
        self.assertIn("cosh(chi/sqrt(6))", branch["canonical_potential"])


if __name__ == "__main__":
    unittest.main()
