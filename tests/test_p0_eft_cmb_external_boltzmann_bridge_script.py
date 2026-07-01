from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_external_boltzmann_bridge import build_payload


class P0EFTCMBExternalBoltzmannBridgeTests(unittest.TestCase):
    def test_bridge_contract_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "external-boltzmann-bridge-contract-written")
        self.assertTrue(payload["proxy_spectra_available"])
        self.assertIn("TT C_ell", payload["expected_outputs"])

    def test_external_validation_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["adapter_written"])
        self.assertFalse(payload["external_solver_run"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
