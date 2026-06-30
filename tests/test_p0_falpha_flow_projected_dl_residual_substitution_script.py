from __future__ import annotations

import unittest

from scripts.build_p0_falpha_flow_projected_dl_residual_substitution import build_payload


class P0FalphaFlowProjectedDLResidualSubstitutionTests(unittest.TestCase):
    def test_flow_projected_substitution_reduces_but_does_not_close(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "flow-projected-dl-substitution-open")
        self.assertTrue(payload["dl_rows_reduced_conditionally"])
        self.assertFalse(payload["falpha_source_derived"])
        self.assertFalse(payload["connection_force_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_substitution_covers_plus_and_minus_dl_rows(self) -> None:
        checks = build_payload()["substitution_checks"]
        sectors = {row["sector"] for row in checks}
        substitutions = " ".join(row["substitution"] for row in checks)

        self.assertEqual(sectors, {"plus", "minus"})
        self.assertIn("D_self L=F_alpha L", substitutions)
        self.assertIn("mirror flow projection", substitutions)

    def test_still_open_keeps_cuu_dlogb_dphi_and_same_l_open(self) -> None:
        open_text = " ".join(build_payload()["still_open"])

        self.assertIn("same-L K/Q_cross", open_text)
        self.assertIn("hE=rho hCuu", open_text)
        self.assertIn("DlogB", open_text)
        self.assertIn("D_phi", open_text)


if __name__ == "__main__":
    unittest.main()
