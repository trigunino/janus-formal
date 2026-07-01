import unittest

from scripts.build_p0_eft_janus_z4_lensing_shape_delta_gate import build_payload


class P0EFTJanusZ4LensingShapeDeltaGateTests(unittest.TestCase):
    def test_shape_delta_gate(self):
        payload = build_payload()
        shape = payload["shape_decomposition"]

        self.assertEqual(payload["status"], "janus-z4-lensing-shape-delta-gate")
        self.assertEqual(payload["delta_channel"], "weyl_lensing_shape")
        self.assertEqual(payload["delta_level"], "kernel/source")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["raw_native_los_used_for_planck"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["unlensed_primary_unchanged"])
        self.assertEqual(payload["phiphi_convention"], "C_L_phiphi")
        self.assertTrue(payload["phiphi_continuity_passed"])
        self.assertTrue(payload["lensed_remapping_continuity_passed"])
        self.assertTrue(payload["physical_remapping_diagnostic_used"])
        self.assertTrue(payload["normalized_shape_diagnostic_used"])
        self.assertTrue(shape["shape_component_present"])
        self.assertTrue(shape["observationally_useful_shape"])
        self.assertGreater(shape["shape_fraction"], 0.10)
        self.assertTrue(payload["lensing_shape_delta_gate_passed"])
        self.assertFalse(payload["nonzero_z4_planck_eligible"])


if __name__ == "__main__":
    unittest.main()
