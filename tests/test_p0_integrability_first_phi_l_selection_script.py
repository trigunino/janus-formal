from __future__ import annotations

import unittest

from scripts.build_p0_integrability_first_phi_l_selection import build_payload, render_markdown


class P0IntegrabilityFirstPhiLSelectionTests(unittest.TestCase):
    def test_artifact_is_source_compatible_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-compatible-integrability-first-route-open")
        self.assertEqual(payload["selection_source"], "dust_image_curl_frobenius_inverse_map")
        self.assertFalse(payload["uses_s_couple_selection"])
        self.assertTrue(payload["source_compatible"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["fit_to_observations"])
        self.assertEqual(payload["free_parameters"], [])

    def test_conditions_include_required_guardrails(self) -> None:
        rows = {row["name"]: row for row in build_payload()["conditions"]}

        self.assertIn("dust_image_curl", rows)
        self.assertIn("frobenius_inverse_map", rows)
        self.assertIn("b4vol_continuity", rows)
        self.assertIn("same_phi_l_cuu_bridge", rows)
        self.assertIn("caustic_multistream_obstruction", rows)
        self.assertIn("B_4vol remains continuous", rows["b4vol_continuity"]["condition"])
        self.assertIn("same phi/L", rows["same_phi_l_cuu_bridge"]["condition"])
        self.assertIn("det dphi=0", rows["caustic_multistream_obstruction"]["condition"])
        self.assertEqual(rows["caustic_multistream_obstruction"]["status"], "obstruction")

    def test_uniqueness_is_not_proved_without_boundary_data(self) -> None:
        uniqueness = build_payload()["uniqueness"]

        self.assertFalse(uniqueness["forces_unique_phi_l"])
        self.assertIn("boundary or initial data", uniqueness["unique_only_if"])
        self.assertIn("single regular inverse map", uniqueness["unique_only_if"])
        self.assertIn("homogeneous", uniqueness["reason"])
        self.assertIn("holonomy", uniqueness["reason"])

    def test_route_rejects_s_couple_and_observational_fit(self) -> None:
        payload = build_payload()
        text = " ".join(payload["route"].values()) + " " + payload["verdict"]

        self.assertIn("dust-image curl", text)
        self.assertIn("Frobenius", text)
        self.assertIn("inverse", text)
        self.assertIn("without S_couple tuning", text)
        self.assertFalse(payload["fit_to_observations"])

    def test_markdown_reports_core_decision(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Uses S_couple selection: False", markdown)
        self.assertIn("Fit to observations: False", markdown)
        self.assertIn("Forces unique phi/L: False", markdown)
        self.assertIn("caustic", markdown)


if __name__ == "__main__":
    unittest.main()
