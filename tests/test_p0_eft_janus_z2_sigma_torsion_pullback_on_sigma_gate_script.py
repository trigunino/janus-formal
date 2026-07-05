import unittest

from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate import build_payload


class P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGateTests(unittest.TestCase):
    def test_torsion_pullback_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["torsion_pullback_ledger_declared"])
        self.assertTrue(payload["declared"]["differential_form_pullback_imported"])
        self.assertTrue(payload["declared"]["Cartan_first_structure_equation_imported"])
        self.assertTrue(payload["declared"]["coframe_connection_pullback_gate_declared"])
        self.assertTrue(payload["closure"]["cartan_torsion_formula_ready"])
        self.assertTrue(payload["closure"]["sigma_pullback_formula_ready"])
        self.assertTrue(payload["partial_subchannels"]["cartan_torsion_formula"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["pullback_formula"]["ready"])

    def test_torsion_pullback_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["Sigma_embedding_ready"])
        self.assertFalse(payload["closure"]["connection_pullback_ready"])
        self.assertFalse(payload["upstream_frontiers"]["coframe_connection_pullback"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["flrw_irreducible_torsion_pullback"]["ready"])
        self.assertEqual(
            payload["upstream_frontiers"]["flrw_irreducible_torsion_pullback"]["primary_blocker"],
            "Sigma_torsion_pullback",
        )
        self.assertFalse(payload["closure"]["FLRW_irreducible_torsion_pullback_ready"])
        self.assertFalse(payload["partial_subchannels"]["flrw_irreducible_split"]["ready"])
        self.assertFalse(payload["torsion_pullback_on_sigma_ready"])
        self.assertIn("pass_coframe_connection_pullback_gate", payload["next_required"])
        self.assertIn("feed_torsion_pullback_to_Immirzi_and_Holst_Nieh_Yan_gates", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
