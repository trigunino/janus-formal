import unittest

from scripts.build_p0_eft_janus_radical_quantum_geometry_bottom_verdict_gate import (
    build_payload,
)


class JanusRadicalQuantumGeometryBottomVerdictTests(unittest.TestCase):
    def test_all_candidate_families_remain_non_predictive_for_alpha(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["candidate_families_audited"])
        self.assertFalse(payload["alpha_generated_no_fit"])
        self.assertTrue(all(not row["can_derive_alpha"] for row in payload["families"]))

    def test_required_chain_is_explicit(self):
        payload = build_payload()

        self.assertIn("topology emergence theorem", payload["new_law_would_need"])
        self.assertIn("mass/alpha operator", payload["new_law_would_need"])
        self.assertFalse(payload["emergent_topology_map_derived"])
        self.assertFalse(payload["emergent_metric_map_derived"])


if __name__ == "__main__":
    unittest.main()
