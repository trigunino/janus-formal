from __future__ import annotations

import unittest

from scripts.build_p0_nonmetricity_mirror_inverse_gate import (
    build_payload,
    render_markdown,
)


class P0NonmetricityMirrorInverseGateTests(unittest.TestCase):
    def test_mirror_identity_is_closed_but_source_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonmetricity-mirror-inverse-identity-closed-source-open")
        self.assertTrue(payload["mirror_identity_closed"])
        self.assertFalse(payload["independent_mirror_n_allowed"])
        self.assertFalse(payload["mirror_source_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_matrix_and_scalar_identities_are_correct(self) -> None:
        payload = build_payload()

        self.assertIn("D_alpha(H^{-1})", payload["matrix_identity"])
        self.assertIn("-H^{-1} N_alpha H^{-1}", payload["matrix_identity"])
        self.assertEqual(payload["scalar_check"]["H_mirror"], "1/h")
        self.assertEqual(payload["scalar_check"]["N_mirror"], "-dh/h**2")
        self.assertEqual(payload["scalar_check"]["Q_plus_Q_mirror"], "0")

    def test_requirements_block_independent_mirror_source(self) -> None:
        text = " ".join(build_payload()["requirements"])

        self.assertIn("same H", text)
        self.assertIn("not a second fitted source one-form", text)
        self.assertIn("curl/integrability", text)
        self.assertIn("Q_mirror=-Q", text)

    def test_markdown_reports_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonmetricity Mirror Inverse", markdown)
        self.assertIn("Independent mirror N allowed: False", markdown)
        self.assertIn("Q_plus_Q_mirror", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
