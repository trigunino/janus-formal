import unittest
import tempfile
from pathlib import Path

import scripts.build_p0_eft_janus_z2_sigma_critical_normalization_builder_gate as gate
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest


class P0EFTJanusZ2SigmaCriticalNormalizationBuilderGateTests(unittest.TestCase):
    def test_gate_declares_active_normalization_requirements(self):
        payload = gate.build_payload()

        self.assertTrue(payload["critical_normalization_builder_ready"])
        self.assertTrue(payload["requires_active_H0_Z2Sigma"])
        self.assertTrue(payload["requires_explicit_gravitational_constant"])
        self.assertFalse(payload["uses_planck_lcdm_H0"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["critical_normalization_values_ready"])

    def test_strict_background_manifest_enables_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "background_scalars.json"
            write_active_z2sigma_background_scalar_manifest(
                manifest_path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                gravitational_constant_si_z2sigma=6.67430e-11,
                scalar_provenance={
                    "H0_Z2Sigma": "active_background_scale",
                    "omega_k_Z2Sigma": "active_projective_curvature",
                    "G_Z2Sigma": "active_low_energy_gravity_convention",
                },
            )
            old_path = gate.BACKGROUND_SCALAR_MANIFEST_PATH
            gate.BACKGROUND_SCALAR_MANIFEST_PATH = manifest_path
            try:
                payload = gate.build_payload()
            finally:
                gate.BACKGROUND_SCALAR_MANIFEST_PATH = old_path

        self.assertTrue(payload["background_scalar_manifest_status"]["valid"])
        self.assertTrue(payload["critical_normalization_values_ready"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
