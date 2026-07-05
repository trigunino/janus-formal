import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import (
    write_active_z2sigma_scale_free_background_primitive_manifest,
    write_active_z2sigma_scale_free_plasma_primitive_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_derivation_frontier_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaBAOScaleFreePrimitiveDerivationFrontierGateTests(unittest.TestCase):
    def test_frontier_blocks_until_split_primitives_exist(self):
        payload = build_payload(
            background_primitive_path=Path("missing_background.json"),
            plasma_primitive_path=Path("missing_plasma.json"),
        )

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertFalse(payload["background_primitive_manifest"]["valid"])
        self.assertFalse(payload["plasma_primitive_manifest"]["valid"])
        self.assertFalse(payload["frontier_closed"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("E_Z2Sigma", payload["derivation_obligations"])
        self.assertIn("Gamma_drag_over_H0_Z2Sigma", payload["derivation_obligations"])

    def test_frontier_closes_with_valid_split_primitives(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            z = np.geomspace(1.0, 1.0e4, 48)
            background = root / "background.json"
            plasma = root / "plasma.json"
            write_active_z2sigma_scale_free_background_primitive_manifest(
                background,
                z,
                lambda zz: 0.3 * (1.0 + zz) ** 1.5 + 0.7,
                omega_k_z2sigma=0.0,
                z_max=float(z[-1]),
                z_d_bracket=(100.0, 2000.0),
                primitive_provenance={
                    "E_Z2Sigma": "active_effective_fluid_derivation_gate",
                    "omega_k_Z2Sigma": "active_projective_curvature_gate",
                },
            )
            write_active_z2sigma_scale_free_plasma_primitive_manifest(
                plasma,
                z,
                lambda zz: np.full_like(np.asarray(zz, dtype=float), 1.0 / 3.0**0.5),
                lambda zz: zz / 1000.0,
                z_max=float(z[-1]),
                z_d_bracket=(100.0, 2000.0),
                primitive_provenance={
                    "c_s_over_c_Z2Sigma": "active_photon_baryon_sound_speed_gate",
                    "Gamma_drag_over_H0_Z2Sigma": "active_thomson_drag_rate_gate",
                },
            )

            payload = build_payload(
                background_primitive_path=background,
                plasma_primitive_path=plasma,
            )

        self.assertTrue(payload["background_primitive_manifest"]["valid"])
        self.assertTrue(payload["plasma_primitive_manifest"]["valid"])
        self.assertTrue(payload["split_primitive_manifests_valid"])
        self.assertTrue(payload["split_primitive_grids_aligned"])
        self.assertTrue(payload["frontier_closed"])
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])
        self.assertFalse(payload["uses_observational_H0_fit"])


if __name__ == "__main__":
    unittest.main()
