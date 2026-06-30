from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_weak_field_weyl_source_chain import build_payload


class P0StueckelbergWeakFieldWeylSourceChainTests(unittest.TestCase):
    def test_chain_available_but_not_tensor_closed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["weak_field_source_to_weyl_chain_available"])
        self.assertTrue(decision["fit_provenance_rejected"])
        self.assertTrue(decision["restricted_metric_ready_flag_available"])
        self.assertFalse(decision["metric_potential_source_derived_from_full_janus"])
        self.assertFalse(decision["full_tensor_weyl_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_contains_poisson_and_trace_free_weyl_steps(self) -> None:
        chain = " ".join(build_payload()["chain"])

        self.assertIn("rho_eff_plus", chain)
        self.assertIn("Delta Phi_lens_plus", chain)
        self.assertIn("gamma1,gamma2", chain)

    def test_guards_reject_fit_and_q_absorption(self) -> None:
        guards = " ".join(build_payload()["guards"])

        self.assertIn("shear_fit", guards)
        self.assertIn("sigma8_fit", guards)
        self.assertIn("not shear residual absorbers", guards)
        self.assertIn("restricted_metric_closure=True", guards)
        self.assertIn("delta G_plus[h_plus]", guards)


if __name__ == "__main__":
    unittest.main()
