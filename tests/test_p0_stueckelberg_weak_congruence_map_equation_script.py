from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_weak_congruence_map_equation import build_payload


class P0StueckelbergWeakCongruenceMapEquationTests(unittest.TestCase):
    def test_weak_condition_is_not_full_isometry(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["decision"]["overconstraint_reduced_vs_isometry"])
        self.assertTrue(payload["decision"]["generic_janus_not_excluded"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(not row["full_isometry_required"] for row in payload["equations"]))

    def test_equations_cancel_only_dust_projection_conditionally(self) -> None:
        payload = build_payload()
        equations = " ".join(row["weak_condition"] for row in payload["equations"])

        self.assertIn("C_plus-minus", equations)
        self.assertIn("C_minus-plus", equations)
        self.assertEqual(payload["decision"]["connection_residual_cancelled_for_dust"], "conditional")
        self.assertFalse(payload["decision"]["accepted_as_final_closure"])

    def test_obligations_prevent_new_axiom_becoming_prediction(self) -> None:
        payload = build_payload()
        obligations = {row["name"]: row for row in payload["closure_obligations"]}

        self.assertTrue(payload["new_axiom_if_imposed"])
        self.assertFalse(obligations["action_origin"]["closed"])
        self.assertFalse(obligations["curl_integrability"]["closed"])
        self.assertIn("Euler-Lagrange", payload["next_step"])


if __name__ == "__main__":
    unittest.main()
