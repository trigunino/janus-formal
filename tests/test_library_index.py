from __future__ import annotations

import unittest

from scripts.index_janus_library import count_keywords


class LibraryIndexTests(unittest.TestCase):
    def test_keyword_count_uses_term_boundaries(self) -> None:
        counts = count_keywords("DESI designates a model description. BAO and CMB are explicit.")

        self.assertEqual(counts["DESI"], 1)
        self.assertEqual(counts["BAO"], 1)
        self.assertEqual(counts["CMB"], 1)


if __name__ == "__main__":
    unittest.main()
