from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_mirror_phi_constraints import build_payload, render_markdown


class P0StueckelbergMirrorPhiConstraintsTests(unittest.TestCase):
    def test_constraints_are_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["artifact"], "stueckelberg-mirror-phi-constraints")
        self.assertEqual(payload["status"], "bounded-constraints-open")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["constraints_uniquely_fix_phi"])

    def test_required_phi_constraints_are_present(self) -> None:
        payload = build_payload()
        requirements = " ".join(row["requirement"] for row in payload["constraints"])

        self.assertTrue(payload["mirror_symmetry_imposed"])
        self.assertTrue(payload["determinant_density_convention_fixed"])
        self.assertTrue(payload["same_l_for_k_and_qcross"])
        self.assertTrue(payload["newtonian_sign_recovery_required"])
        self.assertTrue(payload["no_free_observational_parameters"])
        self.assertIn("Phi_bar is the mirror transform of Phi", requirements)
        self.assertIn("sqrt(-g_plus) Phi", requirements)
        self.assertIn("sqrt(-g_minus) Phi_bar", requirements)
        self.assertIn("same L used in Q_cross", requirements)
        self.assertIn("weak-field dust limit", requirements)
        self.assertIn("may not introduce fit constants", requirements)

    def test_constraints_do_not_claim_unique_phi(self) -> None:
        text = " ".join(row["effect"] for row in build_payload()["constraints"])

        self.assertIn("does not uniquely fix Phi", text)
        self.assertIn("forbids a separate optical-map parameter", text)
        self.assertIn("blocks phenomenological tuning", text)

    def test_markdown_reports_flags(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source derived: False", markdown)
        self.assertIn("New axiom risk: True", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Constraints uniquely fix Phi: False", markdown)


if __name__ == "__main__":
    unittest.main()
