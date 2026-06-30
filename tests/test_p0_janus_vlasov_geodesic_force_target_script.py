from __future__ import annotations

import unittest

from scripts.build_p0_janus_vlasov_geodesic_force_target import build_payload, render_markdown


class P0JanusVlasovGeodesicForceTargetTests(unittest.TestCase):
    def test_covariant_targets_define_force_from_connection(self) -> None:
        payload = build_payload()
        text = " ".join(payload["covariant_targets"])

        self.assertIn("Liouville", text)
        self.assertIn("Gamma^i", text)
        self.assertIn("A^i_Janus", text)
        self.assertTrue(payload["a_janus_no_longer_free_symbol"])

    def test_janus_requirements_keep_same_l_and_measure(self) -> None:
        requirements = " ".join(build_payload()["janus_requirements"])

        self.assertIn("source-derived plus/minus metrics", requirements)
        self.assertIn("same-L", requirements)
        self.assertIn("B_4vol", requirements)
        self.assertIn("X2025 Vlasov/Poisson", requirements)

    def test_weakfield_reduction_links_pi_gate(self) -> None:
        reduction = " ".join(build_payload()["weakfield_reduction_targets"])

        self.assertIn("A_i=-D_i Phi", reduction)
        self.assertIn("G0i shift source", reduction)
        self.assertIn("Pi preservation gate", reduction)

    def test_open_until_source_metric_branch(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["source_metric_required"])
        self.assertTrue(payload["weakfield_metric_force_probe_available"])
        self.assertFalse(payload["phase_space_transport_source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("A_Janus no longer free symbol: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
