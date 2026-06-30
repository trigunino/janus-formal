from __future__ import annotations

import unittest

from scripts.build_p0_connection_force_weak_congruence_reduction import build_payload


class P0ConnectionForceWeakCongruenceReductionTests(unittest.TestCase):
    def test_reduction_is_written_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "weak-congruence-reduction-open")
        self.assertTrue(payload["connection_force_reduced_to_weak_congruence"])
        self.assertEqual(
            payload["weak_congruence_selector_artifact"],
            "p0_janus_weak_congruence_selector_derivation_gate",
        )
        self.assertFalse(payload["weak_congruence_source_derived"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_sectors_reduce_cuu_to_receiver_geodesics(self) -> None:
        text = " ".join(
            row["connection_force"] + " " + row["weak_congruence_target"]
            for row in build_payload()["reduction"]
        )

        self.assertIn("C_plus-minus", text)
        self.assertIn("u_-to+^nu D_plus_nu u_-to+^mu = 0", text)
        self.assertIn("C_minus-plus", text)
        self.assertIn("u_+to-^b D_minus_b u_+to-^a = 0", text)

    def test_obligations_keep_map_source_and_pressure_open(self) -> None:
        obligations = " ".join(build_payload()["proof_obligations"])

        self.assertIn("E_phi/E_L", obligations)
        self.assertIn("inverse-map mirrors", obligations)
        self.assertIn("integrability", obligations)
        self.assertIn("Q_cross", obligations)
        self.assertIn("pressure/Pi", obligations)

    def test_rejects_isometry_and_observational_tuning(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("full metric isometry", rules)
        self.assertIn("transverse directions", rules)
        self.assertIn("observations", rules)
        self.assertIn("R_plus/R_minus", rules)


if __name__ == "__main__":
    unittest.main()
