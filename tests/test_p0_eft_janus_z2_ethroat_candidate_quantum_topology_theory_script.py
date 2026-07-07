import unittest

from scripts.build_p0_eft_janus_z2_ethroat_candidate_quantum_topology_theory import (
    build_payload,
)


class EThroatCandidateQuantumTopologyTheoryTests(unittest.TestCase):
    def test_candidate_has_discrete_family_but_no_unique_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["does_discrete_family_exist"])
        self.assertFalse(payload["does_candidate_select_unique_N"])
        self.assertFalse(payload["candidate_no_fit_alpha_ready"])

    def test_primitive_sector_is_planck_scale(self):
        primitive = build_payload()["primitive_sector_N1"]

        self.assertEqual(primitive["N"], 1)
        self.assertGreater(primitive["L_over_lP"], 0.0)
        self.assertLess(primitive["L_over_lP"], 10.0)

    def test_candidate_is_marked_new_layer(self):
        payload = build_payload()

        self.assertEqual(
            payload["candidate_status"],
            "coherent_new_quantum_topology_layer_but_not_unique_selector",
        )
        self.assertGreaterEqual(len(payload["new_physical_postulates"]), 4)


if __name__ == "__main__":
    unittest.main()
