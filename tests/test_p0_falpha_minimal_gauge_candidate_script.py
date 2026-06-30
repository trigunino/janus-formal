from __future__ import annotations

import unittest

from scripts.build_p0_falpha_minimal_gauge_candidate import build_payload


class P0FalphaMinimalGaugeCandidateTests(unittest.TestCase):
    def test_candidate_is_minimal_but_not_source_law(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "minimal-gauge-candidate-open")
        self.assertTrue(payload["minimal_gauge_declared"])
        self.assertFalse(payload["source_derived_falpha"])
        self.assertFalse(payload["all_transverse_components_fixed_by_source"])
        self.assertFalse(payload["prediction_ready"])

    def test_fixed_components_cover_force_trace_and_lorentz(self) -> None:
        components = {row["component"] for row in build_payload()["fixed_components"]}

        self.assertIn("flow_force_projection", components)
        self.assertIn("continuity_trace_projection", components)
        self.assertIn("lorentz_generator", components)

    def test_gauge_choice_keeps_transverse_components_nonfit(self) -> None:
        gauge = " ".join(build_payload()["gauge_choice"])

        self.assertIn("transverse/off-flow", gauge)
        self.assertIn("Janus source geometry derives", gauge)
        self.assertIn("not by independent fitting", gauge)


if __name__ == "__main__":
    unittest.main()
