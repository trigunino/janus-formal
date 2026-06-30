from __future__ import annotations

import unittest

from scripts.build_p0_zero_rustine_phi_j_l_route_attack_matrix import (
    build_payload,
    render_markdown,
)


class P0ZeroRustinePhiJLRouteAttackMatrixTests(unittest.TestCase):
    def test_all_non_rustine_routes_are_attacked_but_none_selects_general_map(self) -> None:
        payload = build_payload()
        routes = {row["route"]: row for row in payload["routes"]}

        self.assertEqual(payload["status"], "zero-rustine-routes-attacked-no-general-selector-yet")
        self.assertEqual(payload["routes_attacked"], 13)
        self.assertEqual(payload["routes_selecting_phi_j_l"], 0)
        self.assertFalse(payload["any_route_selects_phi_j_l"])
        self.assertIn("noether_split", routes)
        self.assertIn("phase_space_symplectic", routes)
        self.assertIn("lorentz_tetrad", routes)
        self.assertIn("matter_pullback_action_deep", routes)
        self.assertIn("integrability_first", routes)
        self.assertIn("higher_derivative_dl_scouple", routes)
        self.assertIn("curvature_scouple", routes)
        self.assertIn("nonlocal_kernel_scouple", routes)
        self.assertIn("restricted_low_derivative_scouple_no_go", routes)

    def test_proved_obstructions_are_exposed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["b4vol_degeneracy_proved"])
        self.assertTrue(payload["noether_rank_obstruction_proved"])
        self.assertTrue(payload["phase_space_obstruction_proved"])
        self.assertTrue(payload["lorentz_obstruction_proved"])
        self.assertTrue(payload["pullback_dust_skeleton_available"])
        self.assertTrue(payload["matter_pullback_deep_audit_completed"])
        self.assertFalse(payload["pure_matter_pullback_selects_phi_j_l"])
        self.assertTrue(payload["projected_dust_force_shape_derived"])
        self.assertTrue(payload["auxiliary_scouple_remains_ansatz"])
        self.assertTrue(payload["integrability_first_source_compatible"])
        self.assertTrue(payload["higher_derivative_dl_route_produces_pde"])
        self.assertFalse(payload["higher_derivative_dl_route_selects_phi_j_l"])
        self.assertTrue(payload["curvature_scouple_route_produces_equations"])
        self.assertFalse(payload["curvature_scouple_route_selects_phi_j_l"])
        self.assertTrue(payload["nonlocal_kernel_can_select_given_target"])
        self.assertTrue(payload["nonlocal_kernel_arbitrary_target_hiding_risk"])
        self.assertFalse(payload["nonlocal_kernel_route_selects_source_derived_phi_j_l"])
        self.assertTrue(payload["restricted_local_low_derivative_no_go_proved"])
        self.assertFalse(payload["local_no_go_theorem_proved"])

    def test_zero_rustine_policy_is_enforced(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(row["zero_rustine"] for row in payload["routes"]))

    def test_markdown_names_remaining_clean_work(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Routes selecting phi/J/L: 0", markdown)
        self.assertIn("derive independent split Noether/source identity", markdown)
        self.assertIn("derive Hamiltonian/source branch", markdown)
        self.assertIn("derive source rapidity/DL equation", markdown)
        self.assertIn("prove the local low-derivative no-go theorem", markdown)


if __name__ == "__main__":
    unittest.main()
