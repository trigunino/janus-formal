import unittest

from scripts.build_p0_eft_janus_extended2026_observational_claim_map import (
    build_payload,
)


class JanusExtended2026ObservationalClaimMapScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_claim_map_shape(self):
        payload = self.payload
        self.assertEqual(payload["status"], "janus-extended2026-observational-claim-map")
        self.assertGreaterEqual(payload["strictly_reproducible_claim_count"], 4)
        self.assertIn("native_BAO_ruler_validation", payload["forbidden_scope_without_new_paper_level_derivation"])
        claim_ids = {item["claim_id"] for item in payload["claims"]}
        self.assertIn("m18_sn_proxy_shape", claim_ids)
        self.assertIn("x2026_desi_consistency", claim_ids)


if __name__ == "__main__":
    unittest.main()
