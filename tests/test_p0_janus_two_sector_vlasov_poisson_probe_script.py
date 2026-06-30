from __future__ import annotations

import unittest

from scripts.build_p0_janus_two_sector_vlasov_poisson_probe import build_payload, render_markdown


class P0JanusTwoSectorVlasovPoissonProbeScriptTests(unittest.TestCase):
    def test_probe_conserves_mass_and_conjugates_acceleration(self) -> None:
        payload = build_payload()

        self.assertLess(payload["metrics"]["mass_plus_error"], 1e-12)
        self.assertLess(payload["metrics"]["mass_minus_error"], 1e-12)
        self.assertTrue(payload["sector_accelerations_conjugate"])
        self.assertGreaterEqual(payload["metrics"]["min_f_plus_next"], 0.0)

    def test_probe_is_not_physical_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["uses_source_derived_metric_branch"])
        self.assertFalse(payload["uses_same_l_transport"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sector accelerations conjugate: True", markdown)
        self.assertIn("does not close Janus metric/tetrad", markdown)


if __name__ == "__main__":
    unittest.main()
