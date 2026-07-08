import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_paper_native_materialization_audit import (
    build_payload,
)


class Janus2024PaperNativeMaterializationAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_payload_shape(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-paper-native-materialization-audit",
        )
        self.assertTrue(payload["bulk_history_wrapper_present"])
        self.assertTrue(payload["plus_history_materialized"])
        self.assertTrue(payload["minus_history_materialized"])

    def test_remaining_blockers_visible(self):
        payload = self.payload
        self.assertFalse(payload["strict_paper_only_background_materialization_closed"])
        self.assertFalse(payload["paper_only_layer_closed"])
        self.assertTrue(payload["paper_plus_cited_calibration_layer_closed_up_to_minus_init"])
        self.assertTrue(payload["plus_history_fixed_by_cited_sources"])
        self.assertTrue(payload["absolute_normalization_fixed_by_cited_sources_and_ratio"])
        self.assertFalse(payload["minus_initialization_fixed_by_sources"])
        self.assertIn(
            "minus_history_initialization_not_fixed_explicitly_by_2024_text",
            payload["remaining_blockers"],
        )
        self.assertTrue(payload["verdict"]["bulk_materialization_exists"])
        self.assertFalse(payload["verdict"]["bulk_materialization_is_strict_paper_only"])


if __name__ == "__main__":
    unittest.main()
