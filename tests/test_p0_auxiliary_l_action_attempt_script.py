from __future__ import annotations

import unittest

from scripts.build_p0_auxiliary_l_action_attempt import build_payload, render_markdown


class P0AuxiliaryLActionAttemptTests(unittest.TestCase):
    def test_action_attempt_is_ansatz_not_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "auxiliary-action-ansatz-open")
        self.assertTrue(payload["action_written_as_ansatz"])
        self.assertFalse(payload["source_derived_action_found"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_variations_cover_metrics_l_and_noether(self) -> None:
        variations = {row["variation"] for row in build_payload()["variational_tests"]}

        self.assertIn("delta S / delta g_plus", variations)
        self.assertIn("delta S / delta g_minus", variations)
        self.assertIn("delta S / delta L", variations)
        self.assertIn("diagonal diffeomorphism Noether identity", variations)

    def test_rejections_block_fits_and_independent_qcross(self) -> None:
        rules = " ".join(build_payload()["rejection_conditions"])

        self.assertIn("fit lensing", rules)
        self.assertIn("Q_cross", rules)
        self.assertIn("Lorentz constraint", rules)
        self.assertIn("one combined divergence", rules)

    def test_markdown_states_source_derived_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source-derived action found: False", markdown)
        self.assertIn("delta S/delta L", markdown)
        self.assertIn("Prediction ready: False", markdown)

    def test_minimal_scouple_ansatz_ties_qcross_to_l_but_not_two_residuals(self) -> None:
        payload = build_payload()
        ansatz = payload["minimal_scouple_ansatz"]
        result = payload["math_result"]

        self.assertIn("sqrt(-g_plus)", ansatz["density"])
        self.assertIn("I_1=tr", " ".join(ansatz["invariants"]))
        self.assertEqual(ansatz["source_status"], "not found in Janus sources; ansatz only")
        self.assertTrue(result["can_produce_two_metric_variations"])
        self.assertTrue(result["can_tie_qcross_to_l"])
        self.assertFalse(result["can_force_two_residuals_without_extra_structure"])

    def test_symbolic_variation_obligations_cover_k_l_and_noether(self) -> None:
        obligations = {row["object"]: row for row in build_payload()["symbolic_variation_obligations"]}

        self.assertIn("K_plus^{mu nu}", obligations)
        self.assertIn("K_minus^{mu nu}", obligations)
        self.assertIn("E_L", obligations)
        self.assertIn("Noether diagonal identity", obligations)
        self.assertTrue(all(not row["closed"] for row in obligations.values()))


if __name__ == "__main__":
    unittest.main()
