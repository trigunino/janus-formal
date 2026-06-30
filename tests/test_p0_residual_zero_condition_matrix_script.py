from __future__ import annotations

import unittest

from scripts.build_p0_residual_zero_condition_matrix import build_payload


class P0ResidualZeroConditionMatrixTests(unittest.TestCase):
    def test_matrix_rejects_all_branches_for_now(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["matrix_written"])
        self.assertFalse(payload["any_branch_passes"])
        self.assertIsNone(payload["accepted_branch"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_source_measure_branches_have_rows(self) -> None:
        branches = {row["branch"] for row in build_payload()["rows"]}

        self.assertIn("field_equation_4volume_source", branches)
        self.assertIn("slice_dust_flux_source", branches)
        self.assertIn("effective_density_source", branches)

    def test_missing_zero_identities_include_dl_and_measure_terms(self) -> None:
        text = " ".join(
            " ".join(row["must_zero"] + [row["missing_proof"]])
            for row in build_payload()["rows"]
        )

        self.assertIn("D_plus log B_4vol", text)
        self.assertIn("D log V3_dust", text)
        self.assertIn("D rho_eff", text)
        self.assertIn("D L", text)
        self.assertIn("lapse", text)

    def test_global_requirements_block_scalar_shortcuts(self) -> None:
        requirements = " ".join(build_payload()["global_requirements"])

        self.assertIn("R_plus=0", requirements)
        self.assertIn("R_minus=0", requirements)
        self.assertIn("K and Q_cross", requirements)
        self.assertIn("pressure or Pi", requirements)
        self.assertIn("source traceability", requirements)


if __name__ == "__main__":
    unittest.main()
