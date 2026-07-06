from __future__ import annotations

import unittest

from src.janus_lab.z2_so3_regular_throat_collar import (
    regular_throat_collar_frontier_payload,
)


class Z2SO3RegularThroatCollarTests(unittest.TestCase):
    def test_regular_collar_frontier_separates_degenerate_bridge(self) -> None:
        payload = regular_throat_collar_frontier_payload()

        self.assertTrue(payload["radius_law_ready"])
        self.assertFalse(payload["regular_collar_ready"])
        self.assertFalse(payload["DeltaK_derivable_from_collar"])
        self.assertEqual(payload["mpla_degenerate_bridge_branch"]["status"], "diagnostic_only")
        self.assertFalse(payload["mpla_degenerate_bridge_branch"]["active_sigma_regular_branch_compatible"])


if __name__ == "__main__":
    unittest.main()
