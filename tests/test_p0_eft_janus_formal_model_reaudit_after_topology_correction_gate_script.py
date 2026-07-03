import unittest

from scripts.build_p0_eft_janus_formal_model_reaudit_after_topology_correction_gate import build_payload


class P0EFTJanusFormalModelReauditAfterTopologyCorrectionGateTests(unittest.TestCase):
    def test_reaudit_closes_but_keeps_no_fit_false(self):
        payload = build_payload()

        self.assertTrue(payload["reaudit_closed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertTrue(payload["checks"]["z2_cover_kept_as_topological_cover"])
        self.assertTrue(payload["checks"]["z4_not_derived_from_two_fold_cover"])
        self.assertTrue(payload["checks"]["torus_klein_resolved_shadow_loaded"])
        self.assertTrue(payload["checks"]["aps_pin_rp4_reaudit_required"])
        self.assertIn("RP4_Pin_sign_audit", payload["next_required"])
        self.assertIn("order4_lift_or_monodromy_audit", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
