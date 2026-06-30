from __future__ import annotations

import unittest

from scripts.build_janus_linear_beta_vec_closure_gate import build_payload


class JanusLinearBetaVecClosureGateTests(unittest.TestCase):
    def test_gate_is_open_and_blocks_source_derived_label(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "closure-gate-open")
        self.assertFalse(payload["source_derived_beta_allowed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(not row["closed"] for row in payload["closure_matrix"]))

    def test_matrix_covers_linear_map_and_residual_gates(self) -> None:
        gates = {row["gate"] for row in build_payload()["closure_matrix"]}

        self.assertIn("linear_transfer_growth", gates)
        self.assertIn("background_omegas", gates)
        self.assertIn("amplitude", gates)
        self.assertIn("beta_provenance", gates)
        self.assertIn("transport_map", gates)
        self.assertIn("same_map", gates)
        self.assertIn("residuals", gates)

    def test_existing_surfaces_reference_beta_targets(self) -> None:
        surfaces = " ".join(build_payload()["existing_surfaces"])

        self.assertIn("janus_linear_ic_equations_target", surfaces)
        self.assertIn("p0_source_derived_beta_reconstruction_target", surfaces)
        self.assertIn("p0_l_k_qcross_consistency_target", surfaces)


if __name__ == "__main__":
    unittest.main()
