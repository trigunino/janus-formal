from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_so3_signed_schwarzschild_metric_diagnostic import (
    build_payload,
)


class Z2SO3SignedSchwarzschildMetricDiagnosticScriptTests(unittest.TestCase):
    def test_metric_diagnostic_records_horizon_blocker(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["formula"], "f_epsilon(R)=1-epsilon*R_s/R")
        self.assertTrue(payload["attractive_block_degenerate_at_Rs"])
        self.assertFalse(payload["thin_shell_K_formula_ready_at_Rs"])


if __name__ == "__main__":
    unittest.main()
