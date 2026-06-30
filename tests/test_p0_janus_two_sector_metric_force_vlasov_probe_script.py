from __future__ import annotations

import unittest

from scripts.build_p0_janus_two_sector_metric_force_vlasov_probe import build_payload, render_markdown


class P0JanusTwoSectorMetricForceVlasovProbeScriptTests(unittest.TestCase):
    def test_chain_and_conjugacy_are_diagnostic(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["rho_eff_to_phi_to_metric_force_chain_written"])
        self.assertTrue(payload["sector_metric_forces_conjugate"])
        self.assertLess(payload["metrics"]["mass_plus_error"], 1e-12)
        self.assertLess(payload["metrics"]["mass_minus_error"], 1e-12)

    def test_no_source_metric_or_same_l_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_source_selected_janus_metric"])
        self.assertFalse(payload["uses_same_l_transport"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sector metric forces conjugate: True", markdown)
        self.assertIn("not a source-selected Janus metric branch", markdown)


if __name__ == "__main__":
    unittest.main()
