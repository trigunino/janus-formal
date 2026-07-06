import json
import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.run_p0_eft_janus_z2_sigma_effective_bao_diagnostic_frontier import (
    build_payload,
)


class JanusZ2SigmaEffectiveBAODiagnosticFrontierScriptTest(unittest.TestCase):
    def test_diagnostic_frontier_stops_at_missing_primitives(self):
        with tempfile.TemporaryDirectory() as tmp:
            closure = Path(tmp) / "closure.json"
            primitive = Path(tmp) / "missing_primitive.json"
            closure.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "effective_initial_data",
                        "compressed_planck_lcdm_used": False,
                        "archived_z4_reuse_used": False,
                        "observational_fit_used": False,
                        "full_no_fit_prediction_ready": False,
                        "effective_initial_data": {
                            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                            "projected_baryon_number_charge_Z2Sigma": 1.0,
                        },
                        "effective_initial_data_provenance": {
                            "R_Sigma_over_ell_collar_Z2Sigma": "projective_stereographic_Z2_ratio_derivation",
                            "projected_baryon_number_charge_Z2Sigma": "example_declared_superselection_state_initial_data_not_active",
                        },
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(closure_path=closure, primitive_path=primitive)

        self.assertTrue(payload["effective_closure_ready"])
        self.assertFalse(payload["effective_primitive_manifest_available"])
        self.assertFalse(payload["effective_bao_chi2_evaluated"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertIn("E_Z2Sigma(z)", payload["missing_effective_primitives"])

    def test_diagnostic_primitives_move_blocker_to_diagnostic_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            closure = Path(tmp) / "closure.json"
            primitive = Path(tmp) / "primitive.json"
            closure.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "effective_initial_data",
                        "compressed_planck_lcdm_used": False,
                        "archived_z4_reuse_used": False,
                        "observational_fit_used": False,
                        "full_no_fit_prediction_ready": False,
                        "effective_initial_data": {
                            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                            "projected_baryon_number_charge_Z2Sigma": 1.0,
                        },
                        "effective_initial_data_provenance": {
                            "R_Sigma_over_ell_collar_Z2Sigma": "projective_stereographic_Z2_ratio_derivation",
                            "projected_baryon_number_charge_Z2Sigma": "example_declared_superselection_state_initial_data_not_active",
                        },
                    }
                ),
                encoding="utf-8",
            )
            z = [1.0, 900.0, 1000.0, 1100.0, 3000.0]
            primitive.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "effective_primitives",
                        "manifest_kind": "effective_scale_free_primitive_inputs",
                        "compressed_planck_lcdm_used": False,
                        "archived_z4_reuse_used": False,
                        "observational_fit_used": False,
                        "full_no_fit_prediction_ready": False,
                        "source_effective_closure_path": str(closure),
                        "source_effective_closure_sha256": hashlib.sha256(closure.read_bytes()).hexdigest(),
                        "z_grid": z,
                        "E_Z2Sigma": [1.0 for _ in z],
                        "c_s_over_c_Z2Sigma": [0.5 for _ in z],
                        "Gamma_drag_over_H0_Z2Sigma": [zz / 1000.0 for zz in z],
                        "omega_k_Z2Sigma": 0.0,
                        "z_max": 3000.0,
                        "z_d_bracket": [900.0, 1100.0],
                        "primitive_provenance": {
                            "E_Z2Sigma": "diagnostic_constant_background_not_physical",
                            "c_s_over_c_Z2Sigma": "diagnostic_constant_sound_speed_not_physical",
                            "Gamma_drag_over_H0_Z2Sigma": "diagnostic_constant_drag_rate_not_physical",
                            "omega_k_Z2Sigma": "diagnostic_flat_curvature_not_physical",
                        },
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(closure_path=closure, primitive_path=primitive)

        self.assertTrue(payload["effective_primitive_manifest_available"])
        self.assertTrue(payload["effective_bao_chi2_evaluated"])
        self.assertEqual(payload["missing_effective_primitives"], [])
        self.assertFalse(payload["diagnostic_primitives_are_physical_derivation"])
        self.assertEqual(payload["primary_blocker"], "diagnostic_only_not_physical_primitives")


if __name__ == "__main__":
    unittest.main()
