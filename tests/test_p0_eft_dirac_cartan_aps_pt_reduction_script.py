from __future__ import annotations

import unittest

from scripts.build_p0_eft_dirac_cartan_aps_pt_reduction import build_payload, render_markdown


class P0EFTDiracCartanAPSPTReductionTests(unittest.TestCase):
    def test_domain_and_aps_are_specified(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["dirac_cartan_domain_specified"])
        self.assertTrue(status["aps_boundary_condition_specified"])
        self.assertFalse(status["prediction_ready"])

    def test_commutation_is_not_accepted_as_eta_proof(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["theorem_status"]["pt_commutation_rejected_as_insufficient"])
        self.assertIn("not enough", payload["pt_reduction"]["commutation_warning"])
        self.assertIn("PT D_JC PT^-1 = -D_JC", payload["pt_reduction"]["required_relation"])

    def test_pin_minus_reduction_remains_conditional(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["pt_sign_reversal_reduction_encoded"])
        self.assertTrue(status["pin_minus_clifford_lift_rule_encoded"])
        self.assertTrue(status["aps_domain_invariance_rule_encoded"])
        self.assertTrue(status["boundary_chirality_condition_encoded"])
        self.assertTrue(status["orbifold_tetrad_sign_rule_encoded"])
        self.assertTrue(status["projector_compensation_rule_encoded"])
        self.assertTrue(status["trace_torsion_chirality_source_encoded"])
        self.assertTrue(status["eta_zero_if_sign_reversal_proved"])
        self.assertFalse(status["orbifold_tetrad_sign_rule_proved_from_janus_geometry"])
        self.assertFalse(status["trace_torsion_chirality_source_proved"])
        self.assertFalse(status["projector_compensation_proved"])
        self.assertFalse(status["pin_minus_clifford_lift_proved_from_janus_geometry"])
        self.assertFalse(status["aps_domain_invariance_proved_from_janus_geometry"])
        self.assertFalse(status["pt_sign_reversal_proved_from_janus_geometry"])
        self.assertFalse(status["pin_minus_selected_proved"])

    def test_markdown_names_remaining_obligations(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("derive the Pin- Clifford lift rule", markdown)
        self.assertIn("APS domain is preserved", markdown)
        self.assertIn("boundary chirality projection", markdown)
        self.assertIn("E_plus -> -E_minus", markdown)
        self.assertIn("PT Pi_>0 PT^-1 = Pi_<0", markdown)
        self.assertIn("zero modes", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
