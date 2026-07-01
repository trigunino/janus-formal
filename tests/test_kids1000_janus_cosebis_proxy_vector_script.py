from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_cosebis_proxy_vector import cosebis_proxy_shape


class KiDS1000JanusCosebisProxyVectorTests(unittest.TestCase):
    def test_proxy_vector_preserves_en_order_and_dimension(self) -> None:
        en_rows = [
            {"BIN1": 1, "BIN2": 1, "ANGBIN": 1, "ANG": 0.0},
            {"BIN1": 1, "BIN2": 2, "ANGBIN": 2, "ANG": 0.0},
            {"BIN1": 2, "BIN2": 2, "ANGBIN": 1, "ANG": 0.0},
        ]
        nz_rows = [
            {
                "Z_MID": 0.2,
                "BIN1": 1.0,
                "BIN2": 0.0,
                "BIN3": 0.0,
                "BIN4": 0.0,
                "BIN5": 0.0,
            },
            {
                "Z_MID": 0.6,
                "BIN1": 0.0,
                "BIN2": 1.0,
                "BIN3": 0.0,
                "BIN4": 0.0,
                "BIN5": 0.0,
            },
        ]

        rows = cosebis_proxy_shape(en_rows, nz_rows)

        self.assertEqual(len(rows), len(en_rows))
        self.assertEqual([(row["bin1"], row["bin2"], row["angbin"]) for row in rows], [(1, 1, 1), (1, 2, 2), (2, 2, 1)])
        self.assertTrue(all(0.0 <= row["janus_proxy_en_unit_shape"] <= 1.0 for row in rows))


if __name__ == "__main__":
    unittest.main()
