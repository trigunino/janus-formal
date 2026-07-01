from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_local_boltzmann_adapter_runner import build_payload


class P0EFTCMBLocalBoltzmannAdapterRunnerTests(unittest.TestCase):
    def test_local_runner_produces_proxy_output(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "local-boltzmann-adapter-runner-produced-proxy-output")
        self.assertTrue(payload["tables_valid"])
        self.assertTrue(payload["local_proxy_run"])
        self.assertTrue(Path(payload["local_proxy_output"]).exists())

    def test_external_validation_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["external_solver_run"])
        self.assertFalse(payload["external_validation_passed"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
