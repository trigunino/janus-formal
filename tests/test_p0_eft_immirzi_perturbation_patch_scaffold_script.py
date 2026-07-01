from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_perturbation_patch_scaffold import build_payload


class P0EFTImmirziPerturbationPatchScaffoldTests(unittest.TestCase):
    def test_scaffold_lists_missing_perturbation_obligations(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-perturbation-patch-scaffolded")
        self.assertFalse(payload["consistent_perturbation_sector_ready"])
        self.assertFalse(payload["safe_to_activate_geff_background"])
        self.assertIn("momentum_constraint_sigma_etak", payload["missing_obligations"])
        self.assertIn("anisotropic_stress_dgpi", payload["missing_obligations"])
        self.assertIn("photon_baryon_slip", payload["missing_obligations"])


if __name__ == "__main__":
    unittest.main()
