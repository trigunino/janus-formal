import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate import (
    build_payload,
)


class NullSigmaLLBraneTensionDerivationFrontierGateTests(unittest.TestCase):
    def test_frontier_blocks_on_janus_specific_tension_law(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_derivation_ready"])
        self.assertIn("mass_relation", payload["known_relations"])
        self.assertIn("Janus_specific_LL_brane_action_adopted", payload["blocked_by"])
        self.assertIn(
            "derive_chi_LL_abs_inverse_m_without_observational_fit",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
