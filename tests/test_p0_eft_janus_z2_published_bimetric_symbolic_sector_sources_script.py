import unittest

from scripts.build_p0_eft_janus_z2_published_bimetric_symbolic_sector_sources import (
    build_payload,
)


class PublishedBimetricSymbolicSectorSourcesTests(unittest.TestCase):
    def test_writes_symbolic_sources_with_single_absolute_scale(self):
        payload = build_payload()
        manifest = payload["source_manifest"]

        self.assertTrue(payload["symbolic_sector_sources_ready"])
        self.assertFalse(payload["absolute_density_scale_ready"])
        self.assertEqual(manifest["rho_plus0_symbol"], "rho_plus0_abs")
        self.assertAlmostEqual(manifest["rho_minus0_over_rho_plus0"], -19.0)
        self.assertIn("rho_plus0_abs", manifest["dust_shapes"]["rho_minus_of_a"])


if __name__ == "__main__":
    unittest.main()
