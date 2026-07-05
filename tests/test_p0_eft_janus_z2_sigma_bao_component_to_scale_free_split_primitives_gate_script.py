import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_pipeline import REQUIRED_COMPONENT_PROVENANCE
from janus_lab.z2_sigma_component_manifest import (
    Z2SigmaBAOComponentFunctions,
    write_active_z2sigma_bao_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_split_primitives_gate import (
    build_payload,
)


def _components() -> Z2SigmaBAOComponentFunctions:
    zero = lambda x: np.zeros_like(x)
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
        gamma_drag_z2sigma=lambda z: 70.0 * (1.0 + z / 1000.0),
    )


def _provenance() -> dict[str, str]:
    return {field: f"active_gate::{field}" for field in REQUIRED_COMPONENT_PROVENANCE}


def _scalar_provenance() -> dict[str, str]:
    return {
        "H0_Z2Sigma": "active_background_scale_gate",
        "omega_k_Z2Sigma": "active_projective_curvature_gate",
        "G_Z2Sigma": "active_low_energy_gravity_convention",
    }


class P0EFTJanusZ2SigmaBAOComponentToScaleFreeSplitPrimitivesGateTests(unittest.TestCase):
    def test_gate_blocks_without_component_manifest(self):
        payload = build_payload(component_manifest_path=Path("missing_component.json"))

        self.assertFalse(payload["component_manifest_available"])
        self.assertFalse(payload["background_primitive_written"])
        self.assertFalse(payload["plasma_primitive_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["blocker"], "missing active BAO component manifest")

    def test_gate_writes_valid_split_primitives_from_component_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            component = root / "bao_component_inputs.json"
            background = root / "background_primitive.json"
            plasma = root / "plasma_primitive.json"
            write_active_z2sigma_bao_component_manifest(
                component,
                a_grid=np.geomspace(1.0e-4, 1.0, 48),
                z_grid=np.geomspace(1.0, 1.0e4, 48) - 1.0,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                z_d_bracket=(100.0, 2000.0),
                z_max=9999.0,
                components=_components(),
                component_provenance=_provenance(),
                scalar_provenance=_scalar_provenance(),
            )

            payload = build_payload(
                component_manifest_path=component,
                background_primitive_path=background,
                plasma_primitive_path=plasma,
            )

        self.assertTrue(payload["component_manifest_available"])
        self.assertTrue(payload["background_primitive_written"])
        self.assertTrue(payload["plasma_primitive_written"])
        self.assertTrue(payload["background_primitive_valid"])
        self.assertTrue(payload["plasma_primitive_valid"])
        self.assertTrue(payload["split_primitive_grids_aligned"])
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])


if __name__ == "__main__":
    unittest.main()
