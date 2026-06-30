from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_bianchi_noether_gate import build_payload, render_markdown


class P0RouteCSPathBianchiNoetherGateTests(unittest.TestCase):
    def test_gate_records_dependencies_but_blocks_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-bianchi-noether-gate-open")
        self.assertTrue(payload["lorentz_variation_formalized"])
        self.assertTrue(payload["same_l_contract_written"])
        self.assertTrue(payload["stability_screen_written"])
        self.assertTrue(payload["metric_stress_variation_written"])
        self.assertFalse(payload["metric_stress_variation_closed"])
        self.assertTrue(payload["combined_noether_identity_written"])
        self.assertFalse(payload["split_noether_identities_proved"])
        self.assertFalse(payload["bianchi_noether_gate_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_required_tensor_identities(self) -> None:
        rows = {row["identity"]: row for row in build_payload()["noether_rows"]}

        self.assertEqual(
            set(rows),
            {
                "diagonal_diffeomorphism",
                "plus_sector_bianchi",
                "minus_sector_bianchi",
                "same_l_noether_source",
                "stress_from_metric_variation",
            },
        )
        self.assertTrue(all(not row["proved"] for row in rows.values()))
        self.assertIn("R_plus=0", rows["diagonal_diffeomorphism"]["required_for_closure"])
        self.assertIn("K_plus", rows["stress_from_metric_variation"]["formula"])

    def test_tensor_variations_and_mirror_remain_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["k_plus_metric_variation_derived"])
        self.assertFalse(payload["k_minus_metric_variation_derived"])
        self.assertFalse(payload["same_l_noether_source_derived"])
        self.assertFalse(payload["mirror_inverse_identity_proved"])
        self.assertFalse(payload["pressure_pi_tensor_terms_derived"])

    def test_rejection_rules_forbid_scalar_absorption_and_l_split(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("one diagonal Noether identity", rules)
        self.assertIn("Q_det/Q_cross", rules)
        self.assertIn("different L", rules)

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("S_path Bianchi/Noether Gate", markdown)
        self.assertIn("Metric stress variation written: True", markdown)
        self.assertIn("Split Noether identities proved: False", markdown)
        self.assertIn("Bianchi/Noether gate closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
