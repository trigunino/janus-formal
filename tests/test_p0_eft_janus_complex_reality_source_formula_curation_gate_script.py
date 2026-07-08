import unittest

from scripts.build_p0_eft_janus_complex_reality_source_formula_curation_gate import (
    build_payload,
)


class ComplexRealitySourceFormulaCurationGateTests(unittest.TestCase):
    def test_curates_complex_coadjoint_anchors_without_alpha_claim(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["formula_curation_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertTrue(payload["what_document_adds"]["complex_coadjoint_state_space"])
        self.assertTrue(payload["what_document_adds"]["complex_souriau_pairing"])
        self.assertTrue(payload["what_document_does_not_yet_add"]["nonzero_KKS_boundary_density"])
        self.assertTrue(payload["what_document_does_not_yet_add"]["alpha_fixed"])

    def test_includes_needed_formula_blocks(self):
        payload = build_payload()
        anchor_ids = {item["id"] for item in payload["curated_formula_anchors"]}

        self.assertIn("complex_hermite_metric", anchor_ids)
        self.assertIn("complex_lorentz_poincare_group", anchor_ids)
        self.assertIn("complex_moment_space", anchor_ids)
        self.assertIn("complex_duality_pairing", anchor_ids)
        self.assertIn("complex_coadjoint_action", anchor_ids)
        self.assertIn("real_appendix_antisymmetrized_translation_term", anchor_ids)
        self.assertEqual(payload["next_gate"], "ComplexRealityCoadjointStateSpaceGate")


if __name__ == "__main__":
    unittest.main()
