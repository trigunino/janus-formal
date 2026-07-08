import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_frontier_status import (
    build_payload,
)


class Janus2024FrontierStatusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_frontier_status_is_consistent(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-frontier-status",
        )
        self.assertTrue(payload["step1_sn_pipeline"]["source_boundary_reached"])
        self.assertFalse(payload["step2_two_metric_background"]["strict_paper_only_closed"])
        self.assertFalse(payload["step3_absolute_normalization"]["strict_paper_only_closed"])
        self.assertFalse(payload["step4_native_bao_contract"]["native_bao_ruler_closed"])
        self.assertFalse(payload["step5_sector_split_operationality"]["absolute_background_input_ready"])
        self.assertFalse(payload["step6_native_cmb_branch"]["opened"])


if __name__ == "__main__":
    unittest.main()
