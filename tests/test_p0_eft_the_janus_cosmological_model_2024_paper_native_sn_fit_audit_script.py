import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_paper_native_sn_fit_audit import (
    build_payload,
)


class Janus2024PaperNativeSNFitAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_payload_shape(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-paper-native-sn-fit-audit",
        )
        self.assertEqual(payload["dataset"], "JLA 740 SN")
        self.assertEqual(len(payload["procedures"]), 3)

    def test_pipeline_split_is_visible(self):
        payload = self.payload
        self.assertFalse(payload["verdict"]["official_jla_pipeline_recovers_published_q0"])
        self.assertTrue(payload["verdict"]["paper_like_pipeline_recovers_published_q0"])
        self.assertEqual(
            payload["verdict"]["paper_cited_exact_q0_procedure_name"],
            "paper_like_stat_zhel_diag_total",
        )
        self.assertEqual(
            payload["verdict"]["paper_cited_near_chi2_procedure_name"],
            "paper_like_stat_zhel_plain_diag",
        )
        self.assertFalse(
            payload["verdict"]["exact_published_q0_and_chi2_simultaneous_reproduction_closed"]
        )
        self.assertTrue(payload["verdict"]["published_fit_pipeline_is_not_unique_from_paper_text"])


if __name__ == "__main__":
    unittest.main()
