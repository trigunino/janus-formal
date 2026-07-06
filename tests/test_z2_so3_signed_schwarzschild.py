from __future__ import annotations

import unittest

from src.janus_lab.z2_so3_signed_schwarzschild import (
    signed_schwarzschild_df_dR,
    signed_schwarzschild_f,
    signed_schwarzschild_metric_diagnostic,
)


class Z2SO3SignedSchwarzschildTests(unittest.TestCase):
    def test_signed_blocks_at_throat(self) -> None:
        self.assertEqual(signed_schwarzschild_f(1.0, 1.0, +1), 0.0)
        self.assertEqual(signed_schwarzschild_f(1.0, 1.0, -1), 2.0)
        self.assertEqual(signed_schwarzschild_df_dR(1.0, 1.0, +1), 1.0)
        self.assertEqual(signed_schwarzschild_df_dR(1.0, 1.0, -1), -1.0)

    def test_diagnostic_blocks_thin_shell_at_Rs(self) -> None:
        payload = signed_schwarzschild_metric_diagnostic()

        self.assertTrue(payload["attractive_block_degenerate_at_Rs"])
        self.assertFalse(payload["thin_shell_K_formula_ready_at_Rs"])
        self.assertIn("derive a regular throat collar/Kruskal-like chart at R=R_s", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
