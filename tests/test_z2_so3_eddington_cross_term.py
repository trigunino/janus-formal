from __future__ import annotations

import unittest

from src.janus_lab.z2_so3_eddington_cross_term import (
    eddington_cross_term_block,
    eddington_cross_term_collar_diagnostic,
)


class Z2SO3EddingtonCrossTermTests(unittest.TestCase):
    def test_cross_term_block_is_bulk_regular_at_throat(self) -> None:
        block = eddington_cross_term_block(1.0, 1.0)

        self.assertEqual(block["A_TT"], 0.0)
        self.assertEqual(block["B_RR_positive_symbol"], 2.0)
        self.assertEqual(block["C_TR"], -1.0)
        self.assertEqual(block["det_TR_block"], -1.0)

    def test_diagnostic_redirects_to_null_sigma(self) -> None:
        payload = eddington_cross_term_collar_diagnostic()

        self.assertTrue(payload["bulk_TR_block_regular_at_Rs"])
        self.assertTrue(payload["R_const_throat_induced_metric_null"])
        self.assertFalse(payload["current_regular_sigma_hK_formalism_compatible"])
        self.assertIn("choose null Sigma formalism if the Eddington/PT bridge is active", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
