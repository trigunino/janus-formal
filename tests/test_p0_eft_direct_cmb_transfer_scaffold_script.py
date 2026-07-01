from __future__ import annotations

import unittest

from scripts.build_p0_eft_direct_cmb_transfer_scaffold import build_payload


class P0EFTDirectCMBTransferScaffoldTests(unittest.TestCase):
    def test_transfer_scaffold_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "direct-cmb-transfer-scaffold-encoded-spectra-open")
        self.assertTrue(payload["transfer_equations_encoded"])
        self.assertTrue(payload["background_and_ruler_inputs_ready"])

    def test_spectra_and_likelihood_stay_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["cmb_spectra_ready"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])
        self.assertFalse(payload["uses_lcdm_compressed_planck_parameters_as_verdict"])


if __name__ == "__main__":
    unittest.main()
