from __future__ import annotations

import unittest

from scripts.build_p0_transport_branch_closure_obligations import build_payload, render_markdown


class P0TransportBranchClosureObligationsTests(unittest.TestCase):
    def test_obligations_are_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "closure-obligations-open")
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(not row["closed"] for row in payload["obligations"]))

    def test_covers_l_dl_same_l_and_residuals(self) -> None:
        names = {row["name"] for row in build_payload()["obligations"]}

        self.assertIn("admissible_L", names)
        self.assertIn("D_L", names)
        self.assertIn("same_L_for_K_and_Q_cross", names)
        self.assertIn("R_plus_R_minus", names)

    def test_forbids_scalar_shortcuts_and_fit_paths(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("Q_det or Q_cross", shortcuts)
        self.assertIn("lensing fit", shortcuts)
        self.assertIn("polar projection regularity", shortcuts)

    def test_markdown_mentions_both_residuals(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("R_plus", markdown)
        self.assertIn("R_minus", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
