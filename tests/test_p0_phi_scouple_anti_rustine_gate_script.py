from __future__ import annotations

import unittest

from scripts.build_p0_phi_scouple_anti_rustine_gate import build_payload


class P0PhiScoupleAntiRustineGateTests(unittest.TestCase):
    def test_constraints_do_not_force_unique_completion(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "not-forced-family-remains-open")
        self.assertEqual(payload["accepted_action_search_status"], "accepted-scouple-not-found")
        self.assertEqual(payload["closest_published_action"], "M15 bivariational total action")
        self.assertFalse(payload["m15_action_accepted_as_scouple"])
        self.assertEqual(payload["internal_variational_solver_status"], "internal-variational-candidate-open")
        self.assertFalse(payload["internal_solver_unique_phi_forced"])
        self.assertFalse(payload["internal_solver_el_is_transport_equation"])
        self.assertEqual(payload["matter_invariant_solver_status"], "matter-invariant-family-open")
        self.assertFalse(payload["matter_solver_pressure_fixed"])
        self.assertFalse(payload["matter_solver_pi_fixed"])
        self.assertTrue(payload["local_variational_shapes_available"])
        self.assertFalse(payload["variational_acceptance_gate_passed"])
        self.assertFalse(payload["constraints_force_unique_phi_scouple"])
        self.assertTrue(payload["multiple_no_fit_candidates_remain_possible"])
        self.assertFalse(payload["can_adopt_as_published_janus_derivation"])
        self.assertTrue(payload["can_adopt_only_as_explicit_new_axiom"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertTrue(payload["forced_selection_search_available"])
        self.assertFalse(payload["prediction_ready"])

    def test_constraint_tests_cover_source_mirror_l_sign_noether(self) -> None:
        tests = " ".join(row["constraint"] + row["effect"] for row in build_payload()["constraint_tests"])

        self.assertIn("M15 determinant", tests)
        self.assertIn("mirror symmetry", tests)
        self.assertIn("same L", tests)
        self.assertIn("Newtonian sign", tests)
        self.assertIn("Noether", tests)

    def test_family_obstruction_and_rules_block_rustine(self) -> None:
        payload = build_payload()
        obstruction = " ".join(payload["family_obstruction"])
        rules = " ".join(payload["anti_rustine_rules"])

        self.assertIn("scalar invariants", obstruction)
        self.assertIn("not the full variational potential", obstruction)
        self.assertIn("do not use observations", rules)
        self.assertIn("new-axiom label", rules)
        self.assertIn("prediction_ready", rules)

    def test_variational_acceptance_gate_names_open_checks(self) -> None:
        payload = build_payload()
        rows = {row["check"]: row for row in payload["variational_acceptance_rows"]}

        self.assertIn("source_supplied_action", rows)
        self.assertIn("metric_variations", rows)
        self.assertIn("same_l_qcross", rows)
        self.assertIn("split_noether", rows)
        self.assertIn("pressure_pi_extension", rows)
        self.assertTrue(rows["metric_variations"]["local_shape_available"])
        self.assertTrue(rows["same_l_qcross"]["local_shape_available"])
        self.assertFalse(rows["source_supplied_action"]["accepted"])
        self.assertFalse(rows["split_noether"]["accepted"])
        self.assertTrue(rows["pressure_pi_extension"]["local_shape_available"])
        self.assertFalse(rows["pressure_pi_extension"]["accepted"])


if __name__ == "__main__":
    unittest.main()
