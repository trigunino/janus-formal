import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    load_active_z2sigma_flrw_component_manifest,
    write_active_z2sigma_flrw_component_manifest,
)


class Z2SigmaFLRWComponentManifestTests(unittest.TestCase):
    def test_writer_outputs_valid_strict_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "flrw_components.json"
            write_active_z2sigma_flrw_component_manifest(
                path,
                a_grid=[0.5, 1.0],
                flrw_components_over_rho_crit0={
                    field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS
                },
                component_provenance={
                    field: f"active_flrw_gate::{field}" for field in FLRW_COMPONENT_FIELDS
                },
            )

            payload = load_active_z2sigma_flrw_component_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["observational_H0_fit_used"])
        self.assertIn("counterterm_p", payload["flrw_components_over_rho_crit0"])

    def test_writer_rejects_bad_grid_or_forbidden_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            with self.assertRaises(ValueError):
                write_active_z2sigma_flrw_component_manifest(
                    path,
                    a_grid=[1.0, 0.5],
                    flrw_components_over_rho_crit0={
                        field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS
                    },
                    component_provenance={
                        field: f"active_flrw_gate::{field}" for field in FLRW_COMPONENT_FIELDS
                    },
                )
            with self.assertRaises(ValueError):
                write_active_z2sigma_flrw_component_manifest(
                    path,
                    a_grid=[0.5, 1.0],
                    flrw_components_over_rho_crit0={
                        field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS
                    },
                    component_provenance={
                        field: "Planck LCDM" for field in FLRW_COMPONENT_FIELDS
                    },
                )
            valid = path.with_name("valid.json")
            write_active_z2sigma_flrw_component_manifest(
                valid,
                a_grid=[0.5, 1.0],
                flrw_components_over_rho_crit0={
                    field: [0.0, 0.0] for field in FLRW_COMPONENT_FIELDS
                },
                component_provenance={
                    field: f"active_flrw_gate::{field}" for field in FLRW_COMPONENT_FIELDS
                },
            )
            text = valid.read_text(encoding="utf-8").replace(
                '"observational_H0_fit_used": false',
                '"observational_H0_fit_used": true',
            )
            valid.write_text(text, encoding="utf-8")
            with self.assertRaises(ValueError):
                load_active_z2sigma_flrw_component_manifest(valid)


if __name__ == "__main__":
    unittest.main()
