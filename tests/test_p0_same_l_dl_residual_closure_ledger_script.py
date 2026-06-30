from __future__ import annotations

import unittest

from scripts.build_p0_same_l_dl_residual_closure_ledger import build_payload


class P0SameLDLResidualClosureLedgerTests(unittest.TestCase):
    def test_ledger_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "closure-ledger-open")
        self.assertFalse(payload["same_l_closed"])
        self.assertFalse(payload["dl_closed"])
        self.assertFalse(payload["dlogb_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(
            payload["spin_connection_identity_artifact"],
            "p0_same_l_spin_connection_transport_identity_gate",
        )
        self.assertTrue(payload["spin_connection_identity_algebra_closed"])
        self.assertFalse(payload["spin_connection_identity_source_selected"])

    def test_ledger_covers_same_l_dl_dlogb_and_both_residuals(self) -> None:
        obligations = {row["obligation"] for row in build_payload()["ledger"]}

        self.assertIn("same_l_for_k_and_qcross", obligations)
        self.assertIn("lorentz_tetrad_compatibility", obligations)
        self.assertIn("dl_identity", obligations)
        self.assertIn("dlogb_identity", obligations)
        self.assertIn("r_plus_substitution", obligations)
        self.assertIn("r_minus_substitution", obligations)

    def test_no_obligation_is_source_derived_or_closed(self) -> None:
        rows = build_payload()["ledger"]

        self.assertTrue(all(not row["source_derived"] for row in rows))
        self.assertTrue(all(not row["closed"] for row in rows))

    def test_dl_identity_uses_spin_connection_form(self) -> None:
        rows = {row["obligation"]: row for row in build_payload()["ledger"]}

        self.assertIn("partial_alpha L+omega_s,alpha L-L omega_o,alpha", rows["dl_identity"]["required_identity"])
        self.assertFalse(rows["dl_identity"]["source_derived"])
        self.assertFalse(rows["dl_identity"]["closed"])

    def test_existing_surfaces_reference_residual_gates(self) -> None:
        surfaces = " ".join(build_payload()["existing_surfaces"])

        self.assertIn("p0_l_k_qcross_consistency_target", surfaces)
        self.assertIn("bianchi_lorentz_residual_reduction", surfaces)
        self.assertIn("p0_dl_dlogb_identity_targets", surfaces)
        self.assertIn("p0_transport_branch_closure_obligations", surfaces)


if __name__ == "__main__":
    unittest.main()
