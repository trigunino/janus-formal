from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_regular_sigma_collar_algebra_gate import build_payload


class Z2RegularSigmaCollarAlgebraGateScriptTests(unittest.TestCase):
    def test_regular_gate_has_key_condition(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["branch"], "regular_non_null_Sigma")
        self.assertIn("A(0) != 0", payload["key_condition"])


if __name__ == "__main__":
    unittest.main()
