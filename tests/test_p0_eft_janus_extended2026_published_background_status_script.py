import unittest

from scripts.build_p0_eft_janus_extended2026_published_background_status import (
    build_payload,
)


class JanusExtended2026PublishedBackgroundStatusScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_payload_shape(self):
        payload = self.payload
        self.assertEqual(payload["status"], "janus-extended2026-published-background-status")
        self.assertEqual(payload["source_policy"], "strict_active_sources_only")
        self.assertTrue(payload["published_plus_branch_executable"])
        self.assertFalse(payload["native_bao_ruler_closed"])
        self.assertFalse(payload["strict_minus_sector_history_closed"])


if __name__ == "__main__":
    unittest.main()
