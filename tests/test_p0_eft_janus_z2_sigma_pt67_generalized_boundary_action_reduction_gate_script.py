import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_pt67_generalized_boundary_action_reduction_gate import (
    build_payload,
)


def _valid_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "PT67_regular_Sigma",
        "source": "active_derived_boundary_condition",
        "bc_family": "closed_cosmology_generalized_BC",
        "boundary_action_choice": "mixed_h_K_closed_cosmology",
        "reference_geometry_choice": "same_topology_isometric_reference",
        "same_topology_surface_proved": True,
        "variation_principle_well_posed": True,
        "non_fit_provenance": "derived_generalized_closed_cosmology_BC",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "coefficient_status": "derived_not_fitted",
        "boundary_density_coefficients": {
            "lambda_0": 0.0,
            "lambda_R3": 1.0,
            "lambda_K": 0.0,
            "lambda_K2": 0.0,
            "lambda_Kab2": 0.0,
        },
        "boundary_geometry_scalars": {
            "volume_factor_pi2_R3": 2.0,
            "R3_coeff_over_R2": 6.0,
            "K_trace_coeff_over_inv_R": 3.0,
            "K2_coeff_over_inv_R2": 9.0,
            "Kab2_coeff_over_inv_R2": 3.0,
        },
        "reference_geometry_scalars": {
            "volume_factor_pi2_R3": 2.0,
            "R3_coeff_over_R2": 5.0,
            "K_trace_coeff_over_inv_R": 3.0,
            "K2_coeff_over_inv_R2": 9.0,
            "Kab2_coeff_over_inv_R2": 3.0,
        },
    }


class PT67GeneralizedBoundaryActionReductionGateTests(unittest.TestCase):
    def test_missing_boundary_action_blocks_reduction(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(bc_input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["reduction_ready"])
        self.assertIn(
            "derive_generalized_boundary_density_coefficients",
            payload["next_required"],
        )

    def test_derived_boundary_action_reduces_to_symbolic_qren(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bc.json"
            path.write_text(json.dumps(_valid_payload()), encoding="utf-8")
            payload = build_payload(bc_input_path=path)

        self.assertTrue(payload["reduction_ready"])
        reduction = payload["reduction"]
        self.assertTrue(reduction["Q_ren_symbolically_nonzero"])
        self.assertEqual(reduction["Q_ren_polynomial_pi2_units"]["pi2_R1"], 2.0)
        self.assertTrue(reduction["absolute_RSigma_still_required"])
        self.assertFalse(payload["can_write_numeric_Q_boundary_raw"])

    def test_fitted_coefficients_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = _valid_payload()
            bad["coefficient_status"] = "fitted"
            path = Path(tmp) / "bc.json"
            path.write_text(json.dumps(bad), encoding="utf-8")
            payload = build_payload(bc_input_path=path)

        self.assertFalse(payload["reduction_ready"])
        self.assertIn(
            "coefficient_status_must_be_derived_not_fitted",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
