from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_same_l_substitution_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCSpathSameLSubstitutionGateTests(unittest.TestCase):
    def test_same_l_contract_is_written_but_physics_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-same-l-substitution-contract-open")
        self.assertTrue(payload["same_l_substitution_contract_written"])
        self.assertTrue(payload["same_l_algebraic_stack_consistent"])
        self.assertTrue(payload["lorentz_variation_formalized"])
        self.assertTrue(payload["all_slots_require_same_l"])
        self.assertFalse(payload["l_selected_by_spath_el"])
        self.assertFalse(payload["same_l_stack_physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_substitution_rows_cover_required_slots(self) -> None:
        rows = {row["slot"]: row for row in build_payload()["substitution_rows"]}

        self.assertEqual(
            set(rows),
            {
                "spath_el_law",
                "coordinate_bridge",
                "k_stress_transport",
                "qcross_optical_projection",
                "vlasov_moment_transport",
                "mirror_inverse",
            },
        )
        self.assertTrue(all(row["uses_same_l"] for row in rows.values()))
        self.assertFalse(rows["spath_el_law"]["substituted"])
        self.assertFalse(rows["mirror_inverse"]["substituted"])

    def test_forbidden_rows_block_separate_bridges_and_scalar_absorption(self) -> None:
        text = " ".join(build_payload()["forbidden_rows"])

        self.assertIn("L1", text)
        self.assertIn("L2", text)
        self.assertIn("scalar Q_cross", text)
        self.assertIn("Q_det", text)
        self.assertIn("Vlasov", text)
        self.assertFalse(build_payload()["scalar_absorption_allowed"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("S_path Same-L Substitution", markdown)
        self.assertIn("All slots require same L: True", markdown)
        self.assertIn("Same-L stack physics closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
