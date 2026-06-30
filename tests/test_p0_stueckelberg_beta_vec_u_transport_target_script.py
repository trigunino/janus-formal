from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_beta_vec_u_transport_target import build_payload


class P0BetaVecUTransportTargetTests(unittest.TestCase):
    def test_target_is_defined_but_not_closed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertEqual(payload["status"], "derivation-target-open")
        self.assertTrue(decision["beta_vec_u_transport_target_defined"])
        self.assertTrue(decision["local_beta_u_code_available"])
        self.assertTrue(decision["pm_calibrated_beta_diagnostic_available"])
        self.assertFalse(decision["source_derived_beta_available"])
        self.assertFalse(decision["admissible_l_transport_available"])
        self.assertFalse(decision["same_l_for_k_and_qcross_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_requires_source_velocity_and_l_transport(self) -> None:
        chain = " ".join(build_payload()["derivation_chain"])

        self.assertIn("T_plus", chain)
        self.assertIn("theta_s", chain)
        self.assertIn("source_derived_janus_dynamics", chain)
        self.assertIn("u_minus=gamma", chain)
        self.assertIn("L_minus_to_plus u_minus", chain)

    def test_gates_forbid_diagnostic_or_mismatched_transport(self) -> None:
        gates = " ".join(build_payload()["admissibility_gates"])

        self.assertIn("source_derived_janus_dynamics", gates)
        self.assertIn("L^T eta L=eta", gates)
        self.assertIn("K_plus/K_minus", gates)
        self.assertIn("Q_cross", gates)
        self.assertIn("R_plus=0 and R_minus=0", gates)
        self.assertIn("diagnostic only", gates)

    def test_code_surfaces_point_to_existing_closure_gates(self) -> None:
        surfaces = " ".join(build_payload()["code_surfaces"])

        self.assertIn("lorentz_gamma_from_beta_vectors", surfaces)
        self.assertIn("transported_four_velocity_from_beta_vectors", surfaces)
        self.assertIn("build_janus_velocity_ic_closure_target", surfaces)
        self.assertIn("build_p0_l_k_qcross_consistency_target", surfaces)


if __name__ == "__main__":
    unittest.main()
