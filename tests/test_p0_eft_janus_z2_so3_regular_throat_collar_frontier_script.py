from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_so3_regular_throat_collar_frontier import (
    build_payload,
)


class Z2SO3RegularThroatCollarFrontierScriptTests(unittest.TestCase):
    def test_frontier_requires_metric_functions(self) -> None:
        payload = build_payload()

        self.assertIn("A(rho), B(rho), C(rho)", payload["reason_not_ready"])
        self.assertIn(
            "derive A(rho), B(rho), C(rho) from the active Z2 bimetric field equations",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
