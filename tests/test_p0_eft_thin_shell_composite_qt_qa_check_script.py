from __future__ import annotations

import unittest

from scripts.build_p0_eft_thin_shell_composite_qt_qa_check import build_payload, render_markdown


class P0EFTThinShellCompositeQTQACheckTests(unittest.TestCase):
    def test_composite_adds_chiral_generator_but_not_normalization(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["composite_qt_qa_loaded"])
        self.assertTrue(status["trace_only_no_go_confirmed"])
        self.assertTrue(status["chiral_clifford_generator_present_if_qA_nonzero"])
        self.assertTrue(status["idempotence_conditions_derived"])
        self.assertFalse(status["projector_normalization_derived_from_janus"])
        self.assertFalse(status["prediction_ready"])

    def test_projector_conditions_are_explicit(self) -> None:
        check = build_payload()["projector_check"]

        self.assertIn("a^2+b^2=a", check["idempotence_equations"])
        self.assertIn("a=1/2", check["nontrivial_projectors"])
        self.assertIn("(1 +/- C)/2", check["required_normalized_form"])

    def test_pin_minus_candidate_is_not_claimed_final(self) -> None:
        payload = build_payload()

        self.assertIn("sign(Sigma)/sqrt(6)", payload["pin_minus_candidate"]["q_A"])
        self.assertIn("remaining_bridge", payload["pin_minus_candidate"])
        self.assertFalse(payload["theorem_status"]["aps_domain_preserved"])

    def test_markdown_records_normalization_gap(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("projector_normalization_derived_from_janus: False", markdown)
        self.assertIn("derive the shell normalization", markdown)


if __name__ == "__main__":
    unittest.main()
