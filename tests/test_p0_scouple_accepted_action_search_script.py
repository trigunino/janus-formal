from __future__ import annotations

import unittest

from scripts.build_p0_scouple_accepted_action_search import build_payload, render_markdown


class P0ScoupleAcceptedActionSearchTests(unittest.TestCase):
    def test_m15_is_closest_action_but_not_scouple(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "accepted-scouple-not-found")
        self.assertEqual(payload["closest_published_action"], "M15 bivariational total action")
        self.assertTrue(payload["m15_action_accepted_for_field_equations"])
        self.assertFalse(payload["m15_action_accepted_as_scouple"])
        self.assertFalse(payload["independent_scouple_found"])
        self.assertFalse(payload["delta_scouple_delta_l_found"])
        self.assertFalse(payload["prediction_ready"])

    def test_sources_name_scouple_blockers(self) -> None:
        payload = build_payload()
        text = " ".join(
            row["source"]
            + row["action_or_principle"]
            + row["accepted_for"]
            + " ".join(row["passes"])
            + " ".join(row["fails_for_scouple"])
            for row in payload["source_rows"]
        )

        self.assertIn("M15", text)
        self.assertIn("bivariation", text)
        self.assertIn("delta S_couple/delta L", text)
        self.assertIn("Q_cross", text)
        self.assertIn("split Noether", text)
        self.assertIn("Pi transport", text)

    def test_acceptance_requires_pressure_pi_and_no_fit(self) -> None:
        required = " ".join(build_payload()["required_acceptance"])

        self.assertIn("K_plus", required)
        self.assertIn("same L used by Q_cross", required)
        self.assertIn("anisotropic stress Pi", required)
        self.assertIn("no observational fit", required)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("M15 action accepted as S_couple: False", markdown)
        self.assertIn("Independent S_couple found: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
