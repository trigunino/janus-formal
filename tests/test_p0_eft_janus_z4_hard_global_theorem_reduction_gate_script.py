import unittest

from scripts.build_p0_eft_janus_z4_hard_global_theorem_reduction_gate import build_payload


class P0EFTJanusZ4HardGlobalTheoremReductionGateTests(unittest.TestCase):
    def test_reductions_exist_but_atomic_obligations_remain_open(self):
        payload = build_payload()

        self.assertTrue(all(payload["reductions"].values()))
        self.assertFalse(payload["all_reduced_obligations_closed"])
        self.assertFalse(payload["pure_math_model_closed_without_axioms"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertEqual(
            payload["refined_aps_gate"],
            "p0_eft_janus_z4_aps_index_package_obligation_gate",
        )
        self.assertEqual(
            payload["refined_orbifold_gate"],
            "p0_eft_janus_z4_orbifold_cover_ratio_obligation_gate",
        )
        for row in payload["atomic_obligations"].values():
            self.assertFalse(row["closed"])
            self.assertGreater(len(row["missing"]), 0)


if __name__ == "__main__":
    unittest.main()
