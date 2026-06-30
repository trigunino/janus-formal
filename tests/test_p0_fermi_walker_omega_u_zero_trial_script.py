from __future__ import annotations

import unittest

from scripts.build_p0_fermi_walker_omega_u_zero_trial import build_payload


class P0FermiWalkerOmegaUZeroTrialTests(unittest.TestCase):
    def test_trial_is_bounded_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "trial-open")
        self.assertTrue(payload["bounded_p0_artifact"])
        self.assertTrue(payload["equations_written"])
        self.assertTrue(payload["conditional_closure_if_source_law_enforces_fw"])
        self.assertFalse(payload["omega_u_zero_source_derived"])
        self.assertTrue(payload["janus_source_derivation_open"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_equations_write_fw_comoving_route_to_omega_u_zero(self) -> None:
        text = " ".join(row["name"] + row["form"] + row["role"] for row in build_payload()["equations"])

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("Omega_u=u^alpha Omega_alpha", text)
        self.assertIn("e_0=u", text)
        self.assertIn("D_u e_A=(u_A a^B-a_A u^B)e_B", text)
        self.assertIn("Omega_u e_0=0", text)
        self.assertIn("Omega_u u=0", text)

    def test_conditional_closure_requires_source_law_not_convention(self) -> None:
        payload = build_payload()
        closure = " ".join(payload["conditional_closure"])
        open_items = " ".join(payload["open_requirements"])

        self.assertTrue(payload["comoving_e0_equals_u_required"])
        self.assertTrue(payload["fermi_walker_source_law_required"])
        self.assertIn("Janus source law", closure)
        self.assertIn("enforces Fermi-Walker transport", closure)
        self.assertIn("rank-one dust Omega residual closes", closure)
        self.assertIn("not from a frame convention", open_items)

    def test_k_qcross_sharing_is_required_and_open(self) -> None:
        payload = build_payload()
        open_items = " ".join(payload["open_requirements"])
        shortcuts = " ".join(payload["forbidden_shortcuts"])
        verdict = payload["verdict"]

        self.assertTrue(payload["k_qcross_sharing_required"])
        self.assertFalse(payload["k_qcross_sharing_closed"])
        self.assertIn("K transport and Q_cross", open_items)
        self.assertIn("separate Omega for K or Q_cross", shortcuts)
        self.assertIn("same L/Omega must be shared with K and Q_cross", verdict)


if __name__ == "__main__":
    unittest.main()
