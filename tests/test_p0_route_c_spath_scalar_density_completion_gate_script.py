from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_scalar_density_completion_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCSPathScalarDensityCompletionGateTests(unittest.TestCase):
    def test_gate_is_written_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-scalar-density-completion-open")
        self.assertTrue(payload["scalar_density_contract_written"])
        self.assertTrue(payload["reparametrization_requirement_written"])
        self.assertTrue(payload["diagonal_diffeomorphism_scalar_requirements_written"])
        self.assertTrue(payload["mirror_pt_parity_requirement_written"])
        self.assertTrue(payload["same_l_requirement_preserved"])
        self.assertFalse(payload["scalar_density_source_derived"])
        self.assertFalse(payload["scalar_density_complete"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_all_scalar_density_slots(self) -> None:
        rows = {row["slot"]: row for row in build_payload()["completion_rows"]}

        self.assertEqual(
            set(rows),
            {
                "path_measure",
                "C_J_scalar",
                "V_J_scalar",
                "lorentz_transport_scalar",
                "mirror_pt_parity",
                "boundary_density",
            },
        )
        self.assertTrue(all(not row["closed"] for row in rows.values()))
        self.assertIn("C_J", rows["C_J_scalar"]["candidate_form"])
        self.assertIn("V_J", rows["V_J_scalar"]["candidate_form"])
        self.assertIn("L^{-1}", rows["mirror_pt_parity"]["candidate_form"])

    def test_markdown_reports_no_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Scalar-Density Completion Gate", markdown)
        self.assertIn("Scalar density source-derived: False", markdown)
        self.assertIn("Scalar density complete: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
