from __future__ import annotations

import unittest

from scripts.build_p0_omega_u_zero_source_derivation_target import build_payload


class P0OmegaUZeroSourceDerivationTargetTests(unittest.TestCase):
    def test_target_is_bounded_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-derivation-target-open")
        self.assertTrue(payload["rank_one_dust_scope"])
        self.assertTrue(payload["omega_u_zero_would_close_residual"])
        self.assertTrue(payload["closure_is_algebraic_only"])
        self.assertTrue(payload["must_be_source_derived"])
        self.assertTrue(payload["omega_source_law_trial_gate_available"])
        self.assertFalse(payload["fit_choice_allowed"])
        self.assertFalse(payload["source_derivation_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_algebra_states_omega_u_zero_closes_rank_one_residual(self) -> None:
        algebra = " ".join(build_payload()["algebra"].values())

        self.assertIn("T=rho u u", algebra)
        self.assertIn("Omega^T T+T Omega", algebra)
        self.assertIn("Omega_u u=0", algebra)
        self.assertIn("would close this residual", algebra)
        self.assertIn("transport/source law", algebra)

    def test_required_equations_include_transport_and_source_laws(self) -> None:
        rows = build_payload()["required_equations"]
        text = " ".join(row["equation"] + row["form"] + row["status"] for row in rows)

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("Omega_u=u^alpha Omega_alpha", text)
        self.assertIn("Fermi-Walker/comoving tetrad", text)
        self.assertIn("Source congruence", text)
        self.assertIn("K/Q_cross", text)
        self.assertIn("source-law-needed", text)

    def test_blockers_forbid_fit_and_require_shared_source_omega(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])
        shortcuts = " ".join(payload["forbidden_shortcuts"])

        self.assertTrue(payload["fermi_walker_or_comoving_tetrad_required"])
        self.assertTrue(payload["source_congruence_required"])
        self.assertFalse(payload["k_qcross_compatibility_closed"])
        self.assertIn("Janus source equations", blockers)
        self.assertIn("whole congruence", blockers)
        self.assertIn("same L/Omega", blockers)
        self.assertIn("by hand", shortcuts)
        self.assertIn("survey fit", shortcuts)
        self.assertIn("without a source transport law", shortcuts)


if __name__ == "__main__":
    unittest.main()
