from __future__ import annotations

import unittest

from scripts.run_p0_eft_coherent_immirzi_tt_shape_delta import compute


class P0EFTCoherentImmirziTTShapeDeltaTests(unittest.TestCase):
    def test_dry_payload(self) -> None:
        payload = compute(execute=False)

        self.assertEqual(payload["status"], "coherent-immirzi-tt-shape-delta-dry")
        self.assertAlmostEqual(payload["c_coherent_immirzi"], 0.09778424139658529)


if __name__ == "__main__":
    unittest.main()
