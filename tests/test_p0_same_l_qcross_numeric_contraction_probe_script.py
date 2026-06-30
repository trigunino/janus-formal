from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_same_l_qcross_numeric_contraction_probe import (
    ETA,
    build_payload,
    lorentz_like_boost,
    qcross_from_k_contraction,
    render_markdown,
)


class P0SameLQcrossNumericContractionProbeTests(unittest.TestCase):
    def test_same_l_qcross_matches_k_contraction_path(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "numeric-artifact-only")
        self.assertEqual(payload["tooling"], ["numpy"])
        self.assertTrue(payload["same_l_consistent"])
        self.assertLess(payload["same_l_max_residual"], 1e-12)
        for row in payload["probe_rows"]:
            self.assertAlmostEqual(
                row["geometric_qcross"], row["same_l_optical_qcross"], places=12
            )

    def test_independent_optical_l_shortcut_is_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])

        self.assertFalse(payload["independent_optical_l_shortcut_allowed"])
        self.assertGreater(payload["independent_l_min_residual"], 1e-3)
        self.assertIn("independent optical-L shortcut", forbidden)
        self.assertIn("same L used for K contraction", forbidden)

    def test_no_fit_or_absorption_is_used(self) -> None:
        payload = build_payload()
        report = render_markdown(payload)

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_posthoc_qcross"])
        self.assertFalse(payload["uses_posthoc_scalar_absorption"])
        self.assertFalse(payload["uses_qdet_absorption"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("Uses posthoc scalar absorption: False", report)
        self.assertIn("Uses Qdet absorption: False", report)

    def test_toy_covectors_are_null_and_l_is_lorentz_like(self) -> None:
        payload = build_payload()
        transform = lorentz_like_boost(0.30)

        self.assertLess(np.max(np.abs(transform.T @ ETA @ transform - ETA)), 1e-12)
        self.assertLess(payload["k_lorentz_error"], 1e-12)
        self.assertLess(payload["independent_optical_l_error"], 1e-12)
        for row in payload["probe_rows"]:
            self.assertLess(abs(row["null_error"]), 1e-12)

    def test_k_contraction_ratio_matches_closed_form_forward_boost(self) -> None:
        transform = lorentz_like_boost(0.30)
        source_velocity = np.array([1.0, 0.0, 0.0, 0.0])
        forward_covector = np.array([1.0, 1.0, 0.0, 0.0])

        _, qcross = qcross_from_k_contraction(
            transform, forward_covector, source_velocity
        )

        self.assertAlmostEqual(qcross, (1.0 + 0.30) / (1.0 - 0.30), places=12)


if __name__ == "__main__":
    unittest.main()
