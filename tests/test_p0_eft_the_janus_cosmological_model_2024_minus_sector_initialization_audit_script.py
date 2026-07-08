import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_minus_sector_initialization_audit import (
    build_payload,
)


class Janus2024MinusSectorInitializationAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_status_and_verdict(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-minus-sector-initialization-audit",
        )
        self.assertFalse(payload["source_derives_repo_current_minus_initialization_convention"])
        self.assertTrue(payload["minus_sector_initialization_is_source_underdetermined"])

    def test_missing_items_are_explicit(self):
        payload = self.payload
        self.assertIn(
            "explicit_present_day_a_minus_normalization",
            payload["source_missing_items"],
        )
        self.assertIn(
            "explicit_present_day_H_minus_normalization",
            payload["source_missing_items"],
        )
        self.assertIn(
            "explicit_minus_initial_value_rule_equivalent_to_h_minus0_ratio",
            payload["source_missing_items"],
        )


if __name__ == "__main__":
    unittest.main()
