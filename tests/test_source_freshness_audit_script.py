from __future__ import annotations

import unittest

from scripts.build_source_freshness_audit import build_payload


class SourceFreshnessAuditTests(unittest.TestCase):
    def test_new_sources_do_not_close_lensing_blockers(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["local_library_size"], 42)
        self.assertIn("No newly found source removes", payload["verdict"])

    def test_added_sources_are_classified(self) -> None:
        payload = build_payload()
        axes = {row["ref_id"]: row["axis"] for row in payload["new_entries"]}

        self.assertEqual(axes["X2026-questionable-black-holes"], "compact_objects")
        self.assertEqual(axes["X2026-complex-reality"], "math_symmetry")


if __name__ == "__main__":
    unittest.main()
