from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_camb_capability_audit import build_payload


class P0EFTCMB_CAMBCapabilityAuditTests(unittest.TestCase):
    def test_installed_camb_capability_is_detected(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["python_camb_available"])
        self.assertTrue(payload["camb_symbolic_available"])
        self.assertTrue(payload["custom_scalar_sources_available"])
        self.assertTrue(payload["custom_scalar_sources_are_symbolic"])

    def test_tabulated_janus_tables_require_wrapper(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["janus_tables_are_tabulated"])
        self.assertFalse(payload["stock_camb_accepts_tabulated_mu_sigma"])
        self.assertTrue(payload["requires_camb_fork_or_wrapper"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
