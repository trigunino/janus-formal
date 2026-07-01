from __future__ import annotations

from pathlib import Path
import tarfile
import tempfile
import unittest

from scripts.build_kids1000_data_products_inventory import (
    USABLE_PRODUCTS,
    classify_member,
    inventory_tarball,
    parse_fits_headers,
    summarize,
)


class KiDS1000DataProductsInventoryTests(unittest.TestCase):
    def test_classifies_expected_product_names(self) -> None:
        self.assertEqual(classify_member("data/covariance.fits"), "fits_data_product")
        self.assertEqual(classify_member("runs/config.ini"), "pipeline_config")
        self.assertEqual(classify_member("chains/chain_functions.py"), "analysis_script")
        self.assertEqual(classify_member("chains/chain/output_multinest_C.txt"), "posterior_chain")
        self.assertEqual(classify_member("nz/redshift_distribution.dat"), "redshift_distribution")

    def test_inventories_tarball_without_extracting(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tar_path = Path(tmp) / "sample.tgz"
            source = Path(tmp) / "covariance.fits"
            source.write_text("fake", encoding="utf-8")
            with tarfile.open(tar_path, "w:gz") as archive:
                archive.add(source, arcname="kids/covariance.fits")

            rows = inventory_tarball(tar_path)

        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["kind"], "fits_data_product")
        self.assertEqual(summarize(rows), {"fits_data_product": 1})

    def test_cosebis_extension_map_matches_reader_example(self) -> None:
        cosebis = USABLE_PRODUCTS["cosebis"]

        self.assertEqual(cosebis["data_vector_extensions"], ["En"])
        self.assertEqual(cosebis["covariance_extension"], "COVMAT")
        self.assertIn("fiducial", cosebis["role"])

    def test_parse_fits_headers_reads_binary_table_shape(self) -> None:
        primary_cards = [
            "SIMPLE  =                    T",
            "BITPIX  =                    8",
            "NAXIS   =                    0",
            "EXTEND  =                    T",
            "END",
        ]
        primary = "".join(card.ljust(80) for card in primary_cards).encode("ascii")
        image_cards = [
            "XTENSION= 'IMAGE   '",
            "BITPIX  =                  -64",
            "NAXIS   =                    2",
            "NAXIS1  =                    2",
            "NAXIS2  =                    2",
            "PCOUNT  =                    0",
            "GCOUNT  =                    1",
            "EXTNAME = 'COVMAT  '",
            "END",
        ]
        cards = [
            "XTENSION= 'BINTABLE'",
            "BITPIX  =                    8",
            "NAXIS   =                    2",
            "NAXIS1  =                   16",
            "NAXIS2  =                    5",
            "PCOUNT  =                    0",
            "GCOUNT  =                    1",
            "TFIELDS =                    1",
            "TTYPE1  = 'VALUE   '",
            "EXTNAME = 'En      '",
            "END",
        ]
        image = "".join(card.ljust(80) for card in image_cards).encode("ascii")
        header = "".join(card.ljust(80) for card in cards).encode("ascii")
        data = (
            primary.ljust(2880, b" ")
            + image.ljust(2880, b" ")
            + bytes(32).ljust(2880, b" ")
            + header.ljust(2880, b" ")
            + bytes(80).ljust(2880, b" ")
        )

        hdus = parse_fits_headers(data)

        self.assertEqual([hdu["extname"] for hdu in hdus], ["PRIMARY", "COVMAT", "En"])
        self.assertEqual(hdus[2]["naxis2"], 5)
        self.assertEqual(hdus[2]["columns"], ["VALUE"])


if __name__ == "__main__":
    unittest.main()
