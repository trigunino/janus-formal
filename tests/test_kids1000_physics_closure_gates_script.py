from __future__ import annotations

import unittest

from scripts.build_kids1000_physics_closure_gates import build_payload


class KiDS1000PhysicsClosureGatesTests(unittest.TestCase):
    def test_prediction_claim_is_blocked_until_all_gates_close(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["all_closed"])
        self.assertFalse(payload["prediction_claim_allowed"])
        gates = {row["gate"]: row for row in payload["gates"]}
        self.assertFalse(gates["primordial_amplitude"]["closed"])
        self.assertIn("KiDS best-fit", gates["primordial_amplitude"]["forbidden"])


if __name__ == "__main__":
    unittest.main()
