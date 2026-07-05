import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    write_active_z2sigma_flrw_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate import (
    build_payload,
)


def _write_flrw(path: Path) -> None:
    a = np.geomspace(1.0e-3, 1.0, 64)
    components = {field: np.zeros_like(a) for field in FLRW_COMPONENT_FIELDS}
    components["cartan_ghy_rho"] = 0.3 / a**3
    components["counterterm_rho"] = 0.7 * np.ones_like(a)
    components["counterterm_p"] = -0.7 * np.ones_like(a)
    write_active_z2sigma_flrw_component_manifest(
        path,
        a_grid=a,
        flrw_components_over_rho_crit0=components,
        component_provenance={
            field: f"active_flrw_component::{field}" for field in FLRW_COMPONENT_FIELDS
        },
    )


def _write_omega(path: Path, omega_k: float = -0.25) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "scalars": {"omega_k_Z2Sigma": omega_k},
                "scalar_provenance": {
                    "omega_k_Z2Sigma": "active_scale_free_curvature_derivation"
                },
            },
            indent=2,
        ),
        encoding="utf-8",
    )


class P0EFTJanusZ2SigmaFLRWToScaleFreeBackgroundPrimitiveGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        payload = build_payload(
            flrw_component_path=Path("missing_flrw.json"),
            omega_k_path=Path("missing_omega.json"),
            background_primitive_path=Path("missing_background.json"),
        )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["background_primitive_written"])
        self.assertFalse(payload["uses_observational_H0_fit"])

    def test_flrw_and_scale_free_omega_write_background_primitive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            flrw = root / "flrw_components.json"
            omega = root / "omega.json"
            background = root / "background_primitive.json"
            _write_flrw(flrw)
            _write_omega(omega)

            payload = build_payload(
                flrw_component_path=flrw,
                omega_k_path=omega,
                background_primitive_path=background,
            )
            output = json.loads(background.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["background_primitive_valid"])
        self.assertEqual(output["manifest_kind"], "scale_free_background_primitive_inputs")
        self.assertEqual(output["primitive_provenance"]["omega_k_Z2Sigma"], "active_scale_free_curvature_derivation")
        self.assertFalse(output["observational_H0_fit_used"])


if __name__ == "__main__":
    unittest.main()
