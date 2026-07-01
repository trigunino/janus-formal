from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_kernel_residual_audit import build_payload, normalized_en_rows


class KiDS1000JanusHolstKernelResidualAuditTests(unittest.TestCase):
    def test_normalized_en_rows_maps_fits_names(self) -> None:
        rows = [{"BIN1": 1, "BIN2": 2, "ANGBIN": 3}]

        self.assertEqual(normalized_en_rows(rows), [{"bin1": 1, "bin2": 2, "angbin": 3}])

    def test_payload_localizes_all_kernel_variants(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["variants"]), 4)
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("pair_chi2_blocks", payload["variants"][0])
        self.assertIn("tomographic_max_bin_scan", payload["variants"][0])


if __name__ == "__main__":
    unittest.main()
