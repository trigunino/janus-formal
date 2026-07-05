import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_pipeline import REQUIRED_COMPONENT_PROVENANCE
from janus_lab.z2_sigma_component_manifest import (
    Z2SigmaBAOComponentFunctions,
    write_active_z2sigma_bao_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_primitive_chi2_gate import (
    build_payload,
)


def _active_components() -> Z2SigmaBAOComponentFunctions:
    zero = lambda x: np.zeros_like(x)

    def e_of_z(z):
        return np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)

    return Z2SigmaBAOComponentFunctions(
        cartan_ghy_rho=lambda a: 0.3 / a**3,
        cartan_ghy_p=zero,
        holst_nieh_yan_rho=zero,
        holst_nieh_yan_p=zero,
        matter_flux_rho=zero,
        matter_flux_p=zero,
        counterterm_rho=lambda a: 0.7 * np.ones_like(a),
        counterterm_p=lambda a: -0.7 * np.ones_like(a),
        rho_baryon_z2sigma=lambda z: 0.05 * (1.0 + z) ** 3,
        rho_photon_z2sigma=lambda z: 5.0e-5 * (1.0 + z) ** 4,
        gamma_drag_z2sigma=lambda z: 70.0 * e_of_z(z) * ((z + 1.0) / 1001.0),
    )


def _component_provenance() -> dict[str, str]:
    return {field: f"active_gate::{field}" for field in REQUIRED_COMPONENT_PROVENANCE}


def _scalar_provenance() -> dict[str, str]:
    return {
        "H0_Z2Sigma": "active_background_scale_gate",
        "omega_k_Z2Sigma": "active_projective_curvature_gate",
        "G_Z2Sigma": "active_low_energy_gravity_convention",
    }


class P0EFTJanusZ2SigmaBAOComponentToScaleFreePrimitiveChi2GateTests(unittest.TestCase):
    def test_missing_component_manifest_blocks_chain(self):
        payload = build_payload(component_manifest_path=Path("missing_component.json"))

        self.assertFalse(payload["component_to_split_primitives_passed"])
        self.assertFalse(payload["primitive_inputs_assembler_passed"])
        self.assertFalse(payload["bao_chi2_evaluated"])
        self.assertFalse(payload["gate_passed"])

    def test_component_manifest_runs_primitive_chi2_chain(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            component = root / "bao_component_inputs.json"
            write_active_z2sigma_bao_component_manifest(
                component,
                a_grid=np.geomspace(1.0e-5, 1.0, 256),
                z_grid=np.geomspace(1.0, 1.0e5, 256) - 1.0,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                z_d_bracket=None,
                z_max=99999.0,
                components=_active_components(),
                component_provenance=_component_provenance(),
                scalar_provenance=_scalar_provenance(),
            )

            payload = build_payload(
                component_manifest_path=component,
                background_primitive_path=root / "background_primitive.json",
                plasma_primitive_path=root / "plasma_primitive.json",
                primitive_input_path=root / "primitive.json",
                scale_free_input_path=root / "scale_free.json",
            )

        self.assertTrue(payload["component_to_split_primitives_passed"])
        self.assertTrue(payload["primitive_inputs_assembler_passed"])
        self.assertTrue(payload["primitive_chi2_passed"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["Gamma_drag_over_H0_Z2Sigma_available"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(len(payload["prediction_vector"]), 13)
        self.assertEqual(len(payload["residual_vector"]), 13)
        self.assertGreater(payload["chi2_DESI_DR2_BAO"], 0.0)


if __name__ == "__main__":
    unittest.main()
