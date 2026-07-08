import unittest

from scripts.build_p0_eft_janus_extended2026_core_status import build_payload


class JanusExtended2026CoreStatusScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_payload_shape(self):
        payload = self.payload
        self.assertEqual(payload["status"], "janus-extended2026-core-status")
        self.assertTrue(payload["source_bundle_ready"])
        self.assertIn("M30", payload["core_source_ids"])
        self.assertIn("X2025-bimetric-hal", payload["core_source_ids"])
        self.assertIn("X2026-expansion-desi", payload["core_source_ids"])
        self.assertIn(
            "C2024-janus-consistent-hal",
            payload["supporting_cosmology_source_ids"],
        )
        self.assertTrue(payload["executable_components"]["strict_published_plus_branch_present"])
        self.assertFalse(payload["published_background_status"]["native_bao_ruler_closed"])
        self.assertGreaterEqual(
            payload["observational_claim_map"]["strictly_reproducible_claim_count"],
            4,
        )

    def test_current_blockers_remain_visible(self):
        payload = self.payload
        self.assertFalse(payload["native_2026_bao_ruler_executable"])
        self.assertFalse(payload["native_2026_cmb_path_executable"])
        self.assertFalse(payload["observational_closure_ready"])
        self.assertIn(
            "strict_minus_sector_history_not_closed_by_active_sources",
            payload["current_blockers"],
        )
        self.assertIn(
            "native_bao_ruler_derivation_missing",
            payload["current_blockers"],
        )


if __name__ == "__main__":
    unittest.main()
