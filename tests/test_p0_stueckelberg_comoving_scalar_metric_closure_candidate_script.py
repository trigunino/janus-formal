from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_comoving_scalar_metric_closure_candidate import build_payload


class P0ComovingScalarMetricClosureCandidateTests(unittest.TestCase):
    def test_restricted_candidate_passes_without_general_closure(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["restricted_comoving_scalar_closure_candidate_passed"])
        self.assertTrue(decision["promotes_poisson_to_metric_for_restricted_branch"])
        self.assertFalse(decision["general_metric_potential_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_reaches_phi_lens_poisson_equation(self) -> None:
        chain = " ".join(build_payload()["derived_chain"])

        self.assertIn("delta G00_plus=2 Delta Psi_plus", chain)
        self.assertIn("delta S00_plus=rho_plus-rho_minus_eff", chain)
        self.assertIn("Phi_lens_plus=(Phi+Psi)/2=Phi", chain)
        self.assertIn("Delta Phi_lens_plus=4 pi G", chain)

    def test_exclusions_keep_general_verrou_open(self) -> None:
        exclusions = " ".join(build_payload()["exclusions"])

        self.assertIn("non-comoving velocities", exclusions)
        self.assertIn("nonzero anisotropic stress", exclusions)
        self.assertIn("generic tensor perturbations", exclusions)
        self.assertIn("fitted shear amplitude", exclusions)


if __name__ == "__main__":
    unittest.main()
