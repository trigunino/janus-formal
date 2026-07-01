from __future__ import annotations

import unittest

from scripts.build_p0_eft_early_holst_plasma_stress_tensor import build_payload


class P0EFTEarlyHolstPlasmaStressTensorTests(unittest.TestCase):
    def test_stress_tensor_relation_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "early-holst-plasma-stress-tensor-derived-symbolically")
        self.assertTrue(payload["passes_relation_lock"])
        self.assertAlmostEqual(payload["derived_delta_Neff"], payload["target_delta_Neff"])

    def test_full_cmb_still_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["is_derived_geometry"])
        self.assertIn("full CMB likelihood", payload["remaining_obligation"])


if __name__ == "__main__":
    unittest.main()
