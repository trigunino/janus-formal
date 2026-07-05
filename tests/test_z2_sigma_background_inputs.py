import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_background_inputs import (
    build_active_z2sigma_curvature_payload_from_flrw_branch,
    load_active_z2sigma_background_scalar_input_manifest,
)


def _payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "omega_k_Z2Sigma": 0.0,
            "gravitational_constant_si_Z2Sigma": 6.67430e-11,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "omega_k_Z2Sigma": "active_projective_curvature_gate",
            "G_Z2Sigma": "active_low_energy_gravity_convention",
        },
    }


class Z2SigmaBackgroundScalarInputManifestTests(unittest.TestCase):
    def test_loader_accepts_strict_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "background_inputs.json"
            path.write_text(json.dumps(_payload()), encoding="utf-8")

            payload = load_active_z2sigma_background_scalar_input_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["scalars"]["H0_Z2Sigma_km_s_Mpc"], 70.0)

    def test_loader_rejects_forbidden_provenance(self):
        payload = _payload()
        payload["scalar_provenance"]["H0_Z2Sigma"] = "Planck LCDM"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "background_inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_background_scalar_input_manifest(path)

    def test_loader_rejects_observational_h0_fit_flag(self):
        payload = _payload()
        payload["observational_H0_fit_used"] = True
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "background_inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_background_scalar_input_manifest(path)

    def test_curvature_payload_from_flrw_branch_computes_omega_k(self):
        payload = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_background_reuse_used": False,
            "observational_H0_fit_used": False,
            "observational_curvature_fit_used": False,
            "scalars": {
                "H0_Z2Sigma_km_s_Mpc": 70.0,
                "R_curv_Z2Sigma_Mpc": 3000.0,
                "k_Z2Sigma": -1,
            },
            "scalar_provenance": {
                "H0_Z2Sigma": "active_background_scale_gate",
                "R_curv_Z2Sigma": "active_flrw_spatial_metric_branch",
                "k_Z2Sigma": "active_flrw_spatial_metric_branch",
            },
        }

        built = build_active_z2sigma_curvature_payload_from_flrw_branch(payload)

        self.assertIn("omega_k_Z2Sigma", built["scalars"])
        self.assertGreater(built["scalars"]["omega_k_Z2Sigma"], 0.0)
        self.assertIn("active_flrw_spatial_metric_branch", built["scalar_provenance"]["omega_k_Z2Sigma"])

    def test_curvature_payload_from_flrw_branch_rejects_forbidden_provenance(self):
        payload = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_background_reuse_used": False,
            "observational_H0_fit_used": False,
            "observational_curvature_fit_used": True,
            "scalars": {
                "H0_Z2Sigma_km_s_Mpc": 70.0,
                "R_curv_Z2Sigma_Mpc": 3000.0,
                "k_Z2Sigma": -1,
            },
            "scalar_provenance": {
                "H0_Z2Sigma": "active_background_scale_gate",
                "R_curv_Z2Sigma": "active_flrw_spatial_metric_branch",
                "k_Z2Sigma": "active_flrw_spatial_metric_branch",
            },
        }

        with self.assertRaises(ValueError):
            build_active_z2sigma_curvature_payload_from_flrw_branch(payload)


if __name__ == "__main__":
    unittest.main()
