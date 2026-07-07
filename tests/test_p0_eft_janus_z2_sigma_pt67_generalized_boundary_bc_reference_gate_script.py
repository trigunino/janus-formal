import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_pt67_generalized_boundary_bc_reference_gate import (
    build_payload,
)


class PT67GeneralizedBoundaryBCReferenceGateTests(unittest.TestCase):
    def test_standard_same_boundary_references_keep_pt67_zero(self):
        payload = build_payload()

        self.assertTrue(payload["pt67_projection_ready"])
        self.assertTrue(payload["pt67_Q_ren_unit_all_zero"])
        self.assertTrue(payload["same_boundary_references_all_zero"])
        self.assertFalse(payload["can_escape_pt67_zero_without_new_bc"])
        self.assertFalse(payload["generalized_boundary_condition_valid"])

    def test_valid_generalized_boundary_condition_is_accepted_as_route_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bc_path = root / "bc.json"
            bc_path.write_text(
                json.dumps(
                    {
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
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(bc_input_path=bc_path)

        self.assertTrue(payload["generalized_boundary_condition_valid"])
        self.assertTrue(payload["bc_route_can_be_tested"])
        self.assertEqual(payload["next_required"], [])

    def test_fit_boundary_condition_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bc_path = root / "bc.json"
            bc_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "PT67_regular_Sigma",
                        "source": "active_derived_boundary_condition",
                        "bc_family": "closed_cosmology_generalized_BC",
                        "boundary_action_choice": "mixed_h_K_closed_cosmology",
                        "reference_geometry_choice": "same_topology_isometric_reference",
                        "same_topology_surface_proved": True,
                        "variation_principle_well_posed": True,
                        "non_fit_provenance": "BAO_fit_BC",
                        "observational_fit_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(bc_input_path=bc_path)

        self.assertFalse(payload["generalized_boundary_condition_valid"])
        self.assertIn(
            "non_fit_provenance_contains_forbidden_token",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
