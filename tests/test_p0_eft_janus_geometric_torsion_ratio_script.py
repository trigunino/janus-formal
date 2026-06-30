from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_geometric_torsion_ratio import build_payload, render_markdown


class P0EFTJanusGeometricTorsionRatioTests(unittest.TestCase):
    def test_trace_fixed_but_axial_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["janus_geometric_filter_written"])
        self.assertTrue(status["q_T_canonical_trace_fixed"])
        self.assertFalse(status["q_A_fixed_by_geometry"])
        self.assertTrue(status["requires_spin_holonomy_law_for_q_A"])
        self.assertFalse(status["prediction_ready"])

    def test_candidate_ratios_include_trace_first(self) -> None:
        ratios = {row["id"]: row for row in build_payload()["candidate_ratios"]}

        self.assertEqual(ratios["R_trace_only"]["condition"], "q_A = 0, q_T = 1")
        self.assertIn("spin holonomy", ratios["R_paired_axial_trace"]["condition"])

    def test_filters_name_volume_and_parity(self) -> None:
        filters = " ".join(row["name"] + " " + row["effect"] for row in build_payload()["filters"])

        self.assertIn("radion as solder-volume trace", filters)
        self.assertIn("no parity-odd residue", filters)

    def test_markdown_keeps_axial_warning(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("q_A_fixed_by_geometry: False", markdown)
        self.assertIn("spin-holonomy", markdown)


if __name__ == "__main__":
    unittest.main()
