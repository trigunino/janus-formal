import unittest

from janus_lab import published_janus_extended2026_core


class JanusExtended2026CoreTests(unittest.TestCase):
    def test_core_sources_and_eq40(self):
        core = published_janus_extended2026_core()
        self.assertIn("M30", core.source_ids)
        self.assertIn("X2026-expansion-desi", core.source_ids)
        self.assertIn("X2026-variable-constants", core.source_ids)
        eq40 = core.variable_constants_eq40_exponents()
        self.assertEqual(eq40["c_hat"], -0.5)
        self.assertEqual(eq40["g_hat"], -1.0)
        self.assertEqual(eq40["characteristic_length"], 1.0)

    def test_bulk_reference_path_is_normalized(self):
        core = published_janus_extended2026_core()
        path = core.bulk_reference_path(samples=64)
        self.assertAlmostEqual(path.a_plus[-1], 1.0)
        self.assertAlmostEqual(path.e_plus(0.0), 1.0, places=10)
        self.assertGreater(path.redshift_grid()[0], 0.0)


if __name__ == "__main__":
    unittest.main()
