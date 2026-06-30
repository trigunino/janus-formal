from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_two_diffeo_route import build_payload


class P0StueckelbergTwoDiffeoRouteTests(unittest.TestCase):
    def test_route_is_new_axiom_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "stueckelberg-two-diffeomorphism-closure")
        self.assertEqual(payload["status"], "open-new-axiom-candidate")
        self.assertTrue(payload["new_axiom"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["split_noether_identities_derived"])
        self.assertFalse(payload["map_equations_supplied"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_map_options_include_phi_and_l_stueckelberg_fields(self) -> None:
        options = {row["field"]: row for row in build_payload()["map_options"]}

        self.assertIn("phi_minus_to_plus", options)
        self.assertIn("L_minus_to_plus", options)
        self.assertIn("Stueckelberg", options["phi_minus_to_plus"]["role"])
        self.assertIn("Stueckelberg", options["L_minus_to_plus"]["role"])

    def test_candidate_noether_identities_target_both_residuals(self) -> None:
        identities = " ".join(
            row["identity"] + " " + row["closure_target"]
            for row in build_payload()["candidate_split_noether_identities"]
        )

        self.assertIn("R_plus", identities)
        self.assertIn("R_minus", identities)
        self.assertIn("E_phi", identities)
        self.assertIn("E_L", identities)

    def test_required_map_equations_are_listed(self) -> None:
        equations = " ".join(build_payload()["required_equations"])

        self.assertIn("delta S/delta phi", equations)
        self.assertIn("delta S/delta L", equations)
        self.assertIn("inverse consistency", equations)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", equations)

    def test_same_l_is_required_for_k_and_qcross(self) -> None:
        payload = build_payload()
        gate = " ".join(payload["acceptance_gate"])

        self.assertTrue(payload["same_l_for_k_and_qcross"])
        self.assertIn("same L", payload["same_l_requirement"])
        self.assertIn("K_plus/K_minus", payload["same_l_requirement"])
        self.assertIn("Q_cross", payload["same_l_requirement"])
        self.assertIn("use the same L for K transport and Q_cross", gate)

    def test_action_skeleton_and_noether_result_do_not_select_branch(self) -> None:
        payload = build_payload()
        skeleton = " ".join(payload["action_skeleton"])
        noether = " ".join(payload["formal_noether_result"])
        obstruction = " ".join(payload["selection_obstruction"])

        self.assertIn("S_cross", skeleton)
        self.assertIn("variational fields", skeleton)
        self.assertIn("E_phi dphi", noether)
        self.assertIn("E_L D_plus L", noether)
        self.assertIn("covariance alone", noether)
        self.assertIn("chosen by hand", obstruction)
        self.assertIn("does not choose", obstruction)


if __name__ == "__main__":
    unittest.main()
