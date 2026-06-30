from __future__ import annotations

import unittest

from scripts.build_janus_velocity_ic_closure_target import build_payload, render_markdown


class JanusVelocityICClosureTargetTests(unittest.TestCase):
    def test_velocity_relation_is_conditional_not_closed(self) -> None:
        payload = build_payload()
        relation = " ".join(payload["conditional_velocity_relation"])

        self.assertFalse(payload["source_derived_ic_ready"])
        self.assertFalse(payload["velocity_scaffold_closed"])
        self.assertIn("theta_s(k,a)", relation)
        self.assertIn("irrotational scalar modes", relation)

    def test_no_sigma8_or_fit_claim_is_allowed(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_claims"])

        self.assertFalse(payload["sigma8_claim_allowed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("no sigma8 normalization", forbidden)
        self.assertIn("no survey-fit amplitude", forbidden)

    def test_qdet_and_qcross_dependencies_are_explicit(self) -> None:
        report = render_markdown(build_payload())

        self.assertIn("Q_det branch fixed", report)
        self.assertIn("Q_cross/L_minus_to_plus", report)
        self.assertIn("same Janus source equations", report)


if __name__ == "__main__":
    unittest.main()
