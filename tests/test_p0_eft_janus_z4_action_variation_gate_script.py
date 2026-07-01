from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_action_variation_gate import build_payload, write_reports


class P0EFTJanusZ4ActionVariationGateScriptTests(unittest.TestCase):
    def test_el_matching_conditions_recover_rank_one_operator(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["residual_after_substitution"], "Matrix([[0], [0]])")
        self.assertTrue(payload["action_variation_scaffold_ready"])
        self.assertFalse(payload["full_action_variation_closed"])
        self.assertIn("EL_plus", payload["matching_conditions"][0])
        self.assertIn("EL_minus", payload["matching_conditions"][1])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_action_variation_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_action_variation_gate.md").exists())
        self.assertIn("Frechet", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
