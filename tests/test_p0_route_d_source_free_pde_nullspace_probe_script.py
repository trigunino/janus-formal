from __future__ import annotations

import unittest

from scripts.build_p0_route_d_source_free_pde_nullspace_probe import (
    build_payload,
    dirichlet_laplacian,
    periodic_laplacian,
    render_markdown,
    summarize_matrix,
)


class P0RouteDSourceFreePDENullspaceProbeTests(unittest.TestCase):
    def test_probe_excludes_source_free_pde_selectors_without_full_no_go(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-free-pde-nullspace-probe-open")
        self.assertTrue(payload["periodic_kernel_detected"])
        self.assertTrue(payload["dirichlet_invertible_but_boundary_unsourced"])
        self.assertTrue(payload["mass_term_invertible_but_coefficient_unsourced"])
        self.assertTrue(payload["source_free_pde_excluded_as_no_axiom_selector"])
        self.assertFalse(payload["source_fixed_placeholder_is_janus_proof"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_matrix_summaries_distinguish_nullity_from_unsourced_boundary(self) -> None:
        periodic = summarize_matrix("periodic", periodic_laplacian(6), False)
        dirichlet = summarize_matrix("dirichlet", dirichlet_laplacian(6), False)

        self.assertEqual(periodic["nullity"], 1)
        self.assertTrue(periodic["selector_defect"])
        self.assertEqual(dirichlet["nullity"], 0)
        self.assertTrue(dirichlet["selector_defect"])

    def test_markdown_reports_nullspace_probe(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source-Free PDE Nullspace", markdown)
        self.assertIn("Periodic kernel detected: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
