import unittest

from scripts.process_janus_reference_pdf import (
    assess_text_quality,
    keyword_hits,
    parse_page_spec,
)


class JanusReferencePdfProcessingTests(unittest.TestCase):
    def test_rejects_corrupt_native_text_layer(self):
        quality = assess_text_quality("���� ���� " * 20)
        self.assertFalse(quality.is_searchable)
        self.assertGreater(quality.replacement_ratio, 0.1)

    def test_accepts_searchable_scientific_text_and_keywords(self):
        text = (
            "The Janus bimetric model uses a throat, orientation inversion, "
            "negative mass and a Schwarzschild horizon junction with extrinsic curvature. "
        )
        self.assertTrue(assess_text_quality(text).is_searchable)
        self.assertIn("janus", keyword_hits(text))
        self.assertIn("negative_mass", keyword_hits(text))
        self.assertIn("extrinsic_curvature", keyword_hits(text))

    def test_parse_page_spec(self):
        self.assertEqual(parse_page_spec("1,3-5,2"), [1, 2, 3, 4, 5])


if __name__ == "__main__":
    unittest.main()
