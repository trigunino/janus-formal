import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_sector_split_operational_audit import (
    build_payload,
)


class Janus2024SectorSplitOperationalAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_sector_split_boundary_is_explicit(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-sector-split-operational-audit",
        )
        self.assertTrue(payload["relative_sector_split_present"])
        self.assertFalse(payload["operational_absolute_background_input_ready"])
        self.assertTrue(payload["operational_cited_assisted_background_input_ready"])
        self.assertTrue(payload["step5_source_boundary_reached"])


if __name__ == "__main__":
    unittest.main()
