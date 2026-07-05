import tempfile
import unittest
from pathlib import Path

import numpy as np

import scripts.build_p0_eft_janus_z2_sigma_effective_fluid_closure_gate as gate
from janus_lab.z2_sigma_flrw_component_manifest import write_active_z2sigma_flrw_component_manifest


class P0EFTJanusZ2SigmaEffectiveFluidClosureGateTests(unittest.TestCase):
    def test_bibliography_supports_method_but_not_direct_janus_formula(self):
        payload = gate.build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography"]["israel_junction_conditions_checked"])
        self.assertTrue(payload["bibliography"]["brown_york_stress_tensor_checked"])
        self.assertTrue(payload["bibliography"]["cosmological_thin_shell_fluid_checked"])
        self.assertFalse(payload["bibliography"]["direct_janus_z2_sigma_rho_p_formula_found"])

    def test_structural_projection_is_ready_but_numeric_fluid_is_not(self):
        payload = gate.build_payload()

        self.assertTrue(payload["effective_fluid_structural_projection_ready"])
        self.assertTrue(payload["structural"]["T_eff_ab_extraction_formula_ready"])
        self.assertFalse(payload["flrw_component_manifest_status"]["exists"])
        self.assertFalse(payload["flrw_component_manifest_status"]["valid"])
        self.assertFalse(payload["structural"]["T_eff_ab_ready_for_FLRW_projection"])
        self.assertFalse(payload["numeric"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["numeric"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["effective_fluid_numeric_closure_ready"])
        self.assertIn("reduce_rho_eff_and_p_eff_to_functions_of_scale_factor", payload["next_required"])

    def test_valid_flrw_component_manifest_closes_numeric_fluid(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "flrw_components.json"
            a = np.asarray([0.5, 1.0])
            zeros = [0.0, 0.0]
            write_active_z2sigma_flrw_component_manifest(
                path,
                a_grid=a,
                flrw_components_over_rho_crit0={
                    "cartan_ghy_rho": [1.0, 0.5],
                    "cartan_ghy_p": zeros,
                    "holst_nieh_yan_rho": zeros,
                    "holst_nieh_yan_p": zeros,
                    "matter_flux_rho": zeros,
                    "matter_flux_p": zeros,
                    "counterterm_rho": zeros,
                    "counterterm_p": zeros,
                },
                component_provenance={
                    "cartan_ghy_rho": "active_cartan",
                    "cartan_ghy_p": "active_cartan",
                    "holst_nieh_yan_rho": "active_holst",
                    "holst_nieh_yan_p": "active_holst",
                    "matter_flux_rho": "active_flux",
                    "matter_flux_p": "active_flux",
                    "counterterm_rho": "active_counterterm",
                    "counterterm_p": "active_counterterm",
                },
            )
            original = gate.FLRW_COMPONENT_MANIFEST_PATH
            gate.FLRW_COMPONENT_MANIFEST_PATH = path
            try:
                payload = gate.build_payload()
            finally:
                gate.FLRW_COMPONENT_MANIFEST_PATH = original

        self.assertTrue(payload["flrw_component_manifest_status"]["valid"])
        self.assertTrue(payload["numeric"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertTrue(payload["numeric"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertTrue(payload["effective_fluid_numeric_closure_ready"])


if __name__ == "__main__":
    unittest.main()
