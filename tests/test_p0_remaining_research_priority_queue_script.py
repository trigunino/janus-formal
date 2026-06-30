from __future__ import annotations

import unittest

from scripts.build_p0_remaining_research_priority_queue import build_payload, render_markdown


class P0RemainingResearchPriorityQueueTests(unittest.TestCase):
    def test_priority_queue_keeps_prediction_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "remaining-research-priority-queue-active")
        self.assertEqual(payload["priority_count"], 3)
        self.assertFalse(payload["zero_axiom_closure_available"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_priorities_are_ordered(self) -> None:
        tasks = [row["task"] for row in build_payload()["priorities"]]

        self.assertEqual(
            tasks,
            [
                "derive_path_rule_from_action_or_noether",
                "derive_source_stf_operator",
                "formalize_extension_contract_if_needed",
            ],
        )

    def test_markdown_reports_queue(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Remaining Research Priority Queue", markdown)
        self.assertIn("derive_path_rule_from_action_or_noether", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
