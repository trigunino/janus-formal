from __future__ import annotations

import struct
import unittest

from scripts.build_kids1000_cosebis_contract import (
    build_cosebis_contract,
    read_binary_table,
    read_fits_hdus,
    read_image_float64,
)
from scripts.build_survey_data_contract import validate_survey_contract


def fits_block(cards: list[str]) -> bytes:
    return "".join(card.ljust(80) for card in cards + ["END"]).encode("ascii").ljust(2880, b" ")


def sample_fits() -> bytes:
    primary = fits_block(["SIMPLE  =                    T", "BITPIX  =                    8", "NAXIS   =                    0"])
    cov = fits_block(
        [
            "XTENSION= 'IMAGE   '",
            "BITPIX  =                  -64",
            "NAXIS   =                    2",
            "NAXIS1  =                    2",
            "NAXIS2  =                    2",
            "PCOUNT  =                    0",
            "GCOUNT  =                    1",
            "EXTNAME = 'COVMAT  '",
        ]
    )
    en = fits_block(
        [
            "XTENSION= 'BINTABLE'",
            "BITPIX  =                    8",
            "NAXIS   =                    2",
            "NAXIS1  =                   40",
            "NAXIS2  =                    2",
            "PCOUNT  =                    0",
            "GCOUNT  =                    1",
            "TFIELDS =                    5",
            "TTYPE1  = 'BIN1    '",
            "TFORM1  = 'K       '",
            "TTYPE2  = 'BIN2    '",
            "TFORM2  = 'K       '",
            "TTYPE3  = 'ANGBIN  '",
            "TFORM3  = 'K       '",
            "TTYPE4  = 'VALUE   '",
            "TFORM4  = 'D       '",
            "TTYPE5  = 'ANG     '",
            "TFORM5  = 'D       '",
            "EXTNAME = 'En      '",
        ]
    )
    nz = fits_block(
        [
            "XTENSION= 'BINTABLE'",
            "BITPIX  =                    8",
            "NAXIS   =                    2",
            "NAXIS1  =                   64",
            "NAXIS2  =                    2",
            "PCOUNT  =                    0",
            "GCOUNT  =                    1",
            "TFIELDS =                    8",
            "TTYPE1  = 'Z_LOW   '",
            "TFORM1  = 'D       '",
            "TTYPE2  = 'Z_MID   '",
            "TFORM2  = 'D       '",
            "TTYPE3  = 'Z_HIGH  '",
            "TFORM3  = 'D       '",
            "TTYPE4  = 'BIN1    '",
            "TFORM4  = 'D       '",
            "TTYPE5  = 'BIN2    '",
            "TFORM5  = 'D       '",
            "TTYPE6  = 'BIN3    '",
            "TFORM6  = 'D       '",
            "TTYPE7  = 'BIN4    '",
            "TFORM7  = 'D       '",
            "TTYPE8  = 'BIN5    '",
            "TFORM8  = 'D       '",
            "EXTNAME = 'NZ_SOURCE'",
        ]
    )
    cov_data = struct.pack(">4d", 1.0, 0.0, 0.0, 1.0).ljust(2880, b" ")
    en_data = (
        struct.pack(">3q2d", 1, 1, 1, 0.1, 0.5)
        + struct.pack(">3q2d", 1, 1, 2, 0.2, 1.5)
    ).ljust(2880, b" ")
    nz_data = (
        struct.pack(">8d", 0.0, 0.1, 0.2, 1.0, 0.0, 0.0, 0.0, 0.0)
        + struct.pack(">8d", 0.2, 0.3, 0.4, 0.0, 1.0, 0.0, 0.0, 0.0)
    ).ljust(2880, b" ")
    return primary + cov + cov_data + en + en_data + nz + nz_data


class KiDS1000CosebisContractTests(unittest.TestCase):
    def test_reads_image_and_binary_table(self) -> None:
        data = sample_fits()
        hdus = read_fits_hdus(data)

        covariance = read_image_float64(data, hdus[1])
        rows = read_binary_table(data, hdus[2])

        self.assertEqual(covariance, [[1.0, 0.0], [0.0, 1.0]])
        self.assertEqual([row["VALUE"] for row in rows], [0.1, 0.2])

    def test_builds_valid_contract_from_fits_bytes(self) -> None:
        contract = build_cosebis_contract(sample_fits())
        validation = validate_survey_contract(contract)

        self.assertTrue(validation["ready"])
        self.assertEqual(validation["dimension"], 2)
        self.assertEqual(contract["survey_id"], "KiDS-1000")


if __name__ == "__main__":
    unittest.main()
