from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_projected_dust_variation_identity import build_payload


class P0ProjectedDustVariationIdentityTests(unittest.TestCase):
    def test_projected_identity_supplies_transverse_source_conditionally(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["projected_identity_found"])
        self.assertFalse(decision["new_multiplier_needed"])
        self.assertEqual(decision["dust_connection_residual_closed"], "conditional")
        self.assertFalse(payload["prediction_ready"])

    def test_identity_chain_contains_dust_divergence_split(self) -> None:
        payload = build_payload()
        identities = " ".join(row["identity"] for row in payload["identity_chain"])

        self.assertIn("nabla_mu T", identities)
        self.assertIn("T^{mu nu}=rho u^mu u^nu", identities)
        self.assertIn("rho h^nu_sigma", identities)

    def test_obligations_keep_full_closure_open(self) -> None:
        payload = build_payload()
        obligations = " ".join(payload["closure_obligations"])

        self.assertIn("same phi/L", obligations)
        self.assertIn("pressure and anisotropic stress", obligations)
        self.assertFalse(payload["decision"]["full_matter_closed"])


if __name__ == "__main__":
    unittest.main()
