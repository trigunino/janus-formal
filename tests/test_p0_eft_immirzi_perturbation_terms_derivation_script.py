from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_perturbation_terms_derivation import build_payload


class P0EFTImmirziPerturbationTermsDerivationTests(unittest.TestCase):
    def test_terms_scaffold_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-perturbation-terms-derivation-scaffolded")
        self.assertEqual(len(payload["terms"]), 3)
        self.assertFalse(payload["all_terms_derived"])
        self.assertFalse(payload["cambridge_safe_to_patch"])

    def test_all_required_targets_are_present(self) -> None:
        names = {term["name"] for term in build_payload()["terms"]}

        self.assertIn("momentum_constraint_sigma_etak", names)
        self.assertIn("anisotropic_stress_dgpi", names)
        self.assertIn("photon_baryon_slip", names)


if __name__ == "__main__":
    unittest.main()
