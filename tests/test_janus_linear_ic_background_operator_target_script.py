from __future__ import annotations

import unittest

from scripts.build_janus_linear_ic_background_operator_target import build_payload


class JanusLinearICBackgroundOperatorTargetTests(unittest.TestCase):
    def test_required_omega_functions_are_not_closed(self) -> None:
        payload = build_payload()
        functions = {row["name"]: row for row in payload["required_functions"]}

        self.assertFalse(payload["physics_closed"])
        self.assertEqual(functions["Omega_plus(a)"]["status"], "missing_source_derivation")
        self.assertEqual(
            functions["Omega_minus_eff(a)"]["status"],
            "missing_source_derivation",
        )
        self.assertIn("M(a)", payload["operator"]["matrix"])

    def test_transfer_substitutes_remain_forbidden(self) -> None:
        payload = build_payload()
        blocked = " ".join(payload["blocked_outputs"])

        self.assertIn("A_J remains blocked_no_fit", blocked)
        self.assertIn("Lambda-CDM", blocked)
        self.assertIn("constant-Omega", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
