from __future__ import annotations

import unittest

import numpy as np

from scripts.build_kids1000_janus_holst_shape_chi2 import (
    best_amplitude,
    build_payload,
    pair_chi2_blocks,
    residual_rows,
    scale_cut_indices,
    slice_contract,
    tomographic_max_bin_scan,
)


class KiDS1000JanusHolstShapeChi2Tests(unittest.TestCase):
    def test_scale_cut_indices_keep_first_five_modes_per_pair(self) -> None:
        self.assertEqual(scale_cut_indices(total_modes_per_pair=4, kept_modes=2, pair_count=3), [0, 1, 4, 5, 8, 9])

    def test_slice_contract_extracts_observed_and_covariance(self) -> None:
        contract = {
            "observed_vector": [1.0, 2.0, 3.0],
            "covariance": [[1.0, 0.1, 0.2], [0.1, 2.0, 0.3], [0.2, 0.3, 3.0]],
        }
        observed, covariance = slice_contract(contract, [0, 2])

        self.assertTrue(np.allclose(observed, [1.0, 3.0]))
        self.assertTrue(np.allclose(covariance, [[1.0, 0.2], [0.2, 3.0]]))

    def test_best_amplitude_recovers_scale(self) -> None:
        observed = np.asarray([2.0, 4.0])
        shape = np.asarray([1.0, 2.0])
        covariance = np.eye(2)

        amplitude, chi2 = best_amplitude(observed, shape, covariance)

        self.assertAlmostEqual(amplitude, 2.0)
        self.assertAlmostEqual(chi2, 0.0)

    def test_residual_rows_and_pair_blocks_are_machine_readable(self) -> None:
        rows = [
            {"bin1": 1, "bin2": 1, "angbin": 1},
            {"bin1": 1, "bin2": 1, "angbin": 2},
            {"bin1": 1, "bin2": 2, "angbin": 1},
        ]
        observed = np.asarray([1.0, 2.0, 3.0])
        shape = np.asarray([1.0, 1.0, 1.0])
        covariance = np.eye(3)

        residual_table = residual_rows(rows, observed, covariance, shape, 2.0)
        blocks = pair_chi2_blocks(rows, 2.0 * shape - observed, covariance)

        self.assertEqual(len(residual_table), 3)
        self.assertEqual(residual_table[0]["pull_diag"], 1.0)
        self.assertEqual(len(blocks), 2)
        self.assertEqual(blocks[0]["n"], 2)

    def test_tomographic_max_bin_scan_grows_dimension(self) -> None:
        rows = [
            {"bin1": 1, "bin2": 1, "angbin": 1},
            {"bin1": 1, "bin2": 2, "angbin": 1},
            {"bin1": 2, "bin2": 2, "angbin": 1},
        ]
        observed = np.asarray([1.0, 2.0, 3.0])
        shape = np.asarray([1.0, 2.0, 3.0])
        covariance = np.eye(3)

        scan = tomographic_max_bin_scan(rows, observed, covariance, shape)

        self.assertEqual(scan[0]["max_bin"], 1)
        self.assertEqual(scan[0]["n"], 1)
        self.assertEqual(scan[1]["max_bin"], 2)
        self.assertEqual(scan[1]["n"], 3)

    def test_payload_computes_diagnostic_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["residual_rows"]), 75)
        self.assertEqual(len(payload["pair_chi2_blocks"]), 15)
        self.assertEqual(len(payload["tomographic_max_bin_scan"]), 5)
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["chi2_claim_ready"])
        self.assertFalse(payload["gates"]["primordial_amplitude_source_derived"])


if __name__ == "__main__":
    unittest.main()
