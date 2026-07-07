import unittest

from scripts.build_p0_eft_janus_z2_ethroat_quantum_topology_frontier_gate import (
    build_payload,
)


class EThroatQuantumTopologyFrontierGateTests(unittest.TestCase):
    def test_frontier_covers_five_routes(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(set(payload["routes"]), {
            "charge_quantization",
            "vacuum_topological_energy",
            "strong_global_regularity",
            "ll_brane_tension",
            "boundary_action_selector",
        })

    def test_current_assets_do_not_derive_ethroat(self):
        payload = build_payload()

        self.assertTrue(payload["E_throat_equals_E_global_is_structurally_allowed"])
        self.assertFalse(payload["E_throat_derived_from_current_assets"])
        self.assertEqual(payload["strict_no_fit_status"], "blocked")

    def test_candidate_theory_is_marked_as_new_layer(self):
        payload = build_payload()

        self.assertTrue(payload["can_build_candidate_quantum_topology_theory"])
        self.assertEqual(
            payload["candidate_theory_status_if_built_now"],
            "new_physical_postulate_not_current_janus_derivation",
        )
        self.assertGreaterEqual(len(payload["minimal_new_axioms_if_one_builds_it"]), 3)


if __name__ == "__main__":
    unittest.main()
