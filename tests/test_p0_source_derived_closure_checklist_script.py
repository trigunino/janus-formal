from __future__ import annotations

import unittest

from scripts.build_p0_source_derived_closure_checklist import build_payload


class P0SourceDerivedClosureChecklistTests(unittest.TestCase):
    def test_all_p0_source_derivation_items_are_present(self) -> None:
        items = {row["item"] for row in build_payload()["items"]}

        self.assertIn("L transport maps", items)
        self.assertIn("D L and connection-force cancellation", items)
        self.assertIn("Transported continuity", items)
        self.assertIn("Transported force equation", items)
        self.assertIn("K tensor compatibility", items)
        self.assertIn("Matter extension", items)
        self.assertIn("Metric potential / Weyl chain", items)

    def test_checklist_is_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["all_items_source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(row["status"] == "open" for row in payload["items"]))

    def test_each_item_has_source_traceability_hooks(self) -> None:
        for row in build_payload()["items"]:
            self.assertTrue(row["source_traceability_hooks"])
            self.assertTrue(row["must_be_derived_from"])
            self.assertTrue(row["must_not_be_imposed_as"])

    def test_forbids_scalar_absorption_shortcuts(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("scalar Q_cross", forbidden)
        self.assertIn("scalar Q_det", forbidden)
        self.assertIn("raw scale/determinant ratios", forbidden)
        self.assertIn("dust-only", forbidden)

    def test_metric_potential_item_blocks_poisson_and_survey_fit_promotion(self) -> None:
        item = next(
            row for row in build_payload()["items"] if row["item"] == "Metric potential / Weyl chain"
        )
        text = " ".join(
            item["symbols"]
            + item["must_be_derived_from"]
            + item["must_not_be_imposed_as"]
            + item["source_traceability_hooks"]
        )

        self.assertIn("Phi_lens_plus", text)
        self.assertIn("delta G_plus[h_plus]", text)
        self.assertIn("PM Poisson potential promoted directly", text)
        self.assertIn("sigma8/S8", text)
        self.assertIn("metric_potential_promotion_gate", text)


if __name__ == "__main__":
    unittest.main()
