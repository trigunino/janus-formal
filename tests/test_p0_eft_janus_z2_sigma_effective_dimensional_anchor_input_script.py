import unittest

from scripts.write_p0_eft_janus_z2_sigma_effective_dimensional_anchor_input import (
    build_payload,
)


class EffectiveDimensionalAnchorInputScriptTests(unittest.TestCase):
    def test_valid_h0_and_radius_anchors_keep_no_fit_false(self):
        payload = build_payload(
            h0_km_s_mpc=70.0,
            r_curv_mpc=3000.0,
            provenance="declared_boundary_state_scale",
        )

        self.assertEqual(payload["branch"], "effective_initial_state")
        self.assertFalse(payload["no_fit_branch_closed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(
            payload["anchors"]["H0_Z2Sigma"]["scalars"]["H0_Z2Sigma_km_s_Mpc"],
            70.0,
        )
        self.assertEqual(
            payload["anchors"]["R_curv_Z2Sigma"]["scalars"]["R_curv_Z2Sigma_Mpc"],
            3000.0,
        )

    def test_missing_anchor_or_fit_provenance_is_rejected(self):
        with self.assertRaises(ValueError):
            build_payload(provenance="declared_boundary_state_scale")
        with self.assertRaises(ValueError):
            build_payload(h0_km_s_mpc=70.0, provenance="observational fit")


if __name__ == "__main__":
    unittest.main()
