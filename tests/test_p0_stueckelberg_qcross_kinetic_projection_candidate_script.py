from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_qcross_kinetic_projection_candidate import build_payload


class P0QcrossKineticProjectionCandidateTests(unittest.TestCase):
    def test_qcross_projection_shape_is_no_fit_candidate(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["qcross_projection_shape_defined"])
        self.assertTrue(decision["uses_same_distribution"])
        self.assertFalse(decision["source_derived"])
        self.assertFalse(decision["independent_amplitude_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_projection_forms_reject_scalar_amplitude(self) -> None:
        payload = build_payload()
        forms = {row["name"]: row for row in payload["projection_forms"]}

        self.assertEqual(forms["forbidden_scalar_amplitude"]["status"], "rejected")
        self.assertIn("A_fit", forms["forbidden_scalar_amplitude"]["formula"])

    def test_requirements_keep_qdet_separate_and_same_l(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["closure_requirements"])

        self.assertIn("same L", requirements)
        self.assertIn("Q_det", requirements)
        self.assertIn("single-sheet", requirements)


if __name__ == "__main__":
    unittest.main()
