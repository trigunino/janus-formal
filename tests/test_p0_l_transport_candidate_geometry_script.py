from __future__ import annotations

import unittest

from scripts.build_p0_l_transport_candidate_geometry import build_payload, render_markdown


class P0LTransportCandidateGeometryTests(unittest.TestCase):
    def test_artifact_is_bounded_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "research-artifact")
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(len(payload["candidates"]), 4)

    def test_compares_required_candidate_definitions(self) -> None:
        names = {candidate["name"] for candidate in build_payload()["candidates"]}

        self.assertEqual(
            names,
            {
                "raw_tetrad_solder",
                "lorentz_polar_projected_map",
                "local_boost_from_relative_velocity",
                "source_transport_law",
            },
        )

    def test_l_geom_dl_is_computable_but_not_admissible_without_lorentz_proof(self) -> None:
        raw = build_payload()["candidates"][0]

        self.assertEqual(raw["definition"], "L_geom^A_B=e_plus^A_mu E_minus^mu_B")
        self.assertIn("computable from the two spin connections", raw["dl_formula_or_unknowns"])
        self.assertIn("not admissible unless L_geom^T eta L_geom=eta is proved", raw["lorentz_admissibility"])
        self.assertFalse(raw["janus_source_derived"])

    def test_each_candidate_has_required_comparison_fields(self) -> None:
        for candidate in build_payload()["candidates"]:
            self.assertIn("dl_formula_or_unknowns", candidate)
            self.assertIn("lorentz_admissibility", candidate)
            self.assertIn("janus_source_derived", candidate)
            self.assertIn("bianchi_qcross_usability", candidate)

    def test_source_transport_is_target_route_not_closed_result(self) -> None:
        source = build_payload()["candidates"][-1]

        self.assertEqual(source["name"], "source_transport_law")
        self.assertEqual(source["janus_source_derived"], "target-not-yet")
        self.assertIn("unknown F", source["dl_formula_or_unknowns"])
        self.assertIn("only candidate capable of closing Bianchi residuals", source["bianchi_qcross_usability"])

    def test_markdown_renders_gate_and_qcross_language(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Bianchi/Q_cross usability", markdown)
        self.assertIn("L_geom gives a computable DL through spin connections", markdown)


if __name__ == "__main__":
    unittest.main()
