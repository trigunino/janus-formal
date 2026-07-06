from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_so3_eddington_cross_term_collar_diagnostic import (
    build_payload,
)


class Z2SO3EddingtonCrossTermCollarDiagnosticScriptTests(unittest.TestCase):
    def test_cross_term_diagnostic_is_not_regular_sigma_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["formula"]["det_TR"], "-1")
        self.assertFalse(payload["current_regular_sigma_hK_formalism_compatible"])


if __name__ == "__main__":
    unittest.main()
