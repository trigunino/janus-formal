import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_hamiltonian_scalar_targets_gate import (
    build_payload,
)


class BoundaryHamiltonianScalarTargetsGateTests(unittest.TestCase):
    def test_missing_scalars_are_constraint_targets_not_free_densities(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["background_scalars_ready"])
        self.assertFalse(payload["early_plasma_ready"])
        self.assertFalse(payload["all_targets_numeric_ready"])
        for name in ["H0_Z2Sigma", "R_curv_Z2Sigma_m", "N_occ"]:
            self.assertIn(name, payload["targets"])
            self.assertTrue(payload["targets"][name]["not_independent_density"])
            self.assertFalse(payload["targets"][name]["numeric_value_ready"])
        self.assertIn("do_not_fit_H0_Z2Sigma", payload["forbidden_shortcuts"])
        self.assertIn(
            "derive_3plus1_boundary_hamiltonian_projection_for_H0",
            payload["next_required"],
        )

    def test_nocc_remains_state_selection_or_initial_data(self):
        target = build_payload()["targets"]["N_occ"]

        self.assertEqual(target["status"], "initial_state_or_superselection_target")
        self.assertIn("Q_Sigma=N_occ", target["source_route"])
        self.assertIn("effective initial state datum", target["required_derivation"][1])


if __name__ == "__main__":
    unittest.main()
