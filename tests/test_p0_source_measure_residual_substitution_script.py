from __future__ import annotations

import unittest

from scripts.build_p0_source_measure_residual_substitution import build_payload


class P0SourceMeasureResidualSubstitutionTests(unittest.TestCase):
    def test_substitution_is_written_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["substitution_rows_written"])
        self.assertTrue(payload["residual_terms_expanded"])
        self.assertIsNone(payload["accepted_branch"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_source_measure_branches_are_present(self) -> None:
        branches = {row["branch"] for row in build_payload()["substitutions"]}

        self.assertIn("field_equation_4volume_source", branches)
        self.assertIn("slice_dust_flux_source", branches)
        self.assertIn("effective_density_source", branches)

    def test_substitutions_cover_both_residuals_and_open_terms(self) -> None:
        text = " ".join(
            " ".join([row["r_plus_source"], row["r_minus_source"], row["open_obstruction"]])
            for row in build_payload()["substitutions"]
        )

        self.assertIn("D_plus_nu", text)
        self.assertIn("D_minus_nu", text)
        self.assertIn("D log B_4vol", text)
        self.assertIn("D L", text)
        self.assertIn("rho_eff", text)

    def test_zero_conditions_reject_scalar_shortcuts(self) -> None:
        conditions = " ".join(build_payload()["required_zero_conditions"])

        self.assertIn("R_plus", conditions)
        self.assertIn("R_minus", conditions)
        self.assertIn("same L used by K", conditions)
        self.assertIn("Q_cross", conditions)
        self.assertIn("pressure metric/projector and Pi", conditions)
        self.assertIn("no branch mixes", conditions)


if __name__ == "__main__":
    unittest.main()
