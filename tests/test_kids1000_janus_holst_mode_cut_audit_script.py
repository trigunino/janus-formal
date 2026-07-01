from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_mode_cut_audit import (
    build_payload,
    contract_indices_for_modes,
    holst_indices_for_modes,
)


class KiDS1000JanusHolstModeCutAuditTests(unittest.TestCase):
    def test_indices_keep_same_modes_in_each_pair(self) -> None:
        self.assertEqual(contract_indices_for_modes(2, total_modes_per_pair=4, pair_count=3), [0, 1, 4, 5, 8, 9])
        self.assertEqual(holst_indices_for_modes(2, holst_modes_per_pair=3, pair_count=2), [0, 1, 3, 4])

    def test_payload_scans_modes_one_to_five(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["rows"]), 5)
        self.assertEqual(payload["rows"][0]["kept_modes_per_pair"], 1)
        self.assertEqual(payload["rows"][-1]["dimension"], 75)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
