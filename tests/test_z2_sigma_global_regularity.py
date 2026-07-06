import unittest

from src.janus_lab.z2_sigma_global_regularity import (
    validate_global_regular_component_payload,
)


def _payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_components",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": [1.0, 2.0, 3.0],
        "normal_frame_holonomy_defect": [1.0, 0.0, 1.0],
        "collar_endpoint_mismatch": [0.0, 0.0, 0.0],
        "junction_bianchi_defect": [0.0, 0.0, 0.0],
        "root_tolerance": 1.0e-12,
        "component_provenance": {
            "normal_frame_holonomy_defect": "active_collar_connection",
            "collar_endpoint_mismatch": "active_deck_pullback",
            "junction_bianchi_defect": "active_surface_bianchi",
        },
    }


class Z2SigmaGlobalRegularityTest(unittest.TestCase):
    def test_selects_unique_ratio_when_freg_has_single_zero(self):
        payload = validate_global_regular_component_payload(_payload())
        self.assertEqual(payload["regularity_roots"], [2.0])
        self.assertTrue(payload["R_Sigma_over_ell_collar_selected"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_rejects_forbidden_provenance(self):
        payload = _payload()
        payload["component_provenance"]["normal_frame_holonomy_defect"] = "Planck fit"
        with self.assertRaisesRegex(ValueError, "Forbidden"):
            validate_global_regular_component_payload(payload)

    def test_rejects_negative_defect_components(self):
        payload = _payload()
        payload["junction_bianchi_defect"][1] = -1.0
        with self.assertRaisesRegex(ValueError, "nonnegative"):
            validate_global_regular_component_payload(payload)


if __name__ == "__main__":
    unittest.main()
