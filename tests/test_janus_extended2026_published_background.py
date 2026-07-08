import unittest

from janus_lab import published_janus_extended2026_background


class JanusExtended2026PublishedBackgroundTests(unittest.TestCase):
    def test_published_background_shapes(self):
        background = published_janus_extended2026_background()
        self.assertLess(background.q0, 0.0)
        self.assertGreater(background.z_max, 0.0)
        self.assertAlmostEqual(background.e_plus(0.0), 1.0, places=12)
        self.assertGreater(background.open_marker(0.5), 0.0)
        self.assertGreater(background.dm_unscaled_basis(0.5), 0.0)
        self.assertGreater(background.dh_unscaled_basis(0.5), 0.0)


if __name__ == "__main__":
    unittest.main()
