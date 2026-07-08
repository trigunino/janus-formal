import unittest

from scripts.build_p0_eft_janus_complex_reality_eq131_kks_projection_gate import (
    build_payload,
)


class ComplexRealityEq131KKSProjectionGateTests(unittest.TestCase):
    def test_raw_eq131_requires_kks_projection(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["published_eq131_accepted_as_source_anchor"])
        self.assertFalse(
            payload["raw_eq131_translation_term_preserves_antihermitian_M_generically"]
        )
        self.assertTrue(payload["kks_ready_term_preserves_antihermitian_M"])
        self.assertTrue(payload["kks_ready_term_matches_real_appendix_pattern"])
        self.assertFalse(payload["blocks_state_space_gate"])


if __name__ == "__main__":
    unittest.main()
