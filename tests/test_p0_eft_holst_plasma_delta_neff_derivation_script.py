from __future__ import annotations

import unittest

from scripts.build_p0_eft_holst_plasma_delta_neff_derivation import build_payload


class P0EFTHolstPlasmaDeltaNeffDerivationTests(unittest.TestCase):
    def test_delta_neff_derivation_attempt_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "holst-plasma-delta-neff-derivation-attempted")
        self.assertGreater(payload["target_delta_Neff"], 0.0)
        self.assertIn("best_candidate", payload)

    def test_existing_constants_find_close_candidate_but_not_derivation(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["delta_Neff_candidate_from_existing_constants"])
        self.assertTrue(payload["candidate_is_close"])
        self.assertFalse(payload["is_derived_geometry"])
        self.assertLess(payload["best_candidate"]["abs_residual"], payload["tolerance"])


if __name__ == "__main__":
    unittest.main()
