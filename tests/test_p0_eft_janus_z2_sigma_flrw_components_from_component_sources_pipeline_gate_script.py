import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate import (
    build_payload,
)


def _component_payload(fields):
    a_grid = [0.25, 0.5, 1.0]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid,
        "flrw_components_over_rho_crit0": {
            field: [0.1, 0.2, 0.3] for field in fields
        },
        "component_provenance": {
            field: f"active {field} derivation" for field in fields
        },
    }


def _matter_flux_payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "component_route": "transparent_sigma_zero_flux",
        "active_sigma_transparency_derived": True,
        "a_grid": [0.25, 0.5, 1.0],
        "flrw_components_over_rho_crit0": {
            "matter_flux_rho": [0.0, 0.0, 0.0],
            "matter_flux_p": [0.0, 0.0, 0.0],
        },
        "component_provenance": {
            "matter_flux_rho": "active Sigma transparency derivation",
            "matter_flux_p": "active Sigma transparency derivation",
        },
    }


class FLRWComponentsFromComponentSourcesPipelineGateTests(unittest.TestCase):
    def test_missing_inputs_block_pipeline(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                cartan_path=root / "missing_cartan.json",
                holst_path=root / "missing_holst.json",
                counterterm_path=root / "missing_counterterm.json",
                matter_flux_path=root / "missing_matter_flux.json",
                partial_input_path=root / "partial.json",
                flrw_input_path=root / "flrw_inputs.json",
                flrw_manifest_path=root / "flrw.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "flrw_component_source_manifests")
        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertIn("non_matter", payload["upstream_frontiers"])
        self.assertIn("matter_flux_merge", payload["upstream_frontiers"])
        self.assertIn("manifest_writer", payload["upstream_frontiers"])
        self.assertIn(
            "cartan_ghy_component",
            payload["upstream_frontiers"]["non_matter"]["upstream_frontiers"],
        )
        self.assertTrue(
            payload["upstream_frontiers"]["non_matter"]["nearest_frontier"][
                "diagnostic_only"
            ]
        )
        self.assertIn(
            "zero_matter_flux_component",
            payload["upstream_frontiers"]["matter_flux_merge"]["upstream_frontiers"],
        )
        self.assertTrue(payload["nearest_flrw_components_frontier"]["diagnostic_only"])

    def test_component_sources_write_flrw_component_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cartan = root / "cartan.json"
            holst = root / "holst.json"
            counterterm = root / "counterterm.json"
            matter_flux = root / "matter_flux.json"
            flrw_manifest = root / "flrw.json"
            cartan.write_text(
                json.dumps(_component_payload(["cartan_ghy_rho", "cartan_ghy_p"])),
                encoding="utf-8",
            )
            holst.write_text(
                json.dumps(_component_payload(["holst_nieh_yan_rho", "holst_nieh_yan_p"])),
                encoding="utf-8",
            )
            counterterm.write_text(
                json.dumps(_component_payload(["counterterm_rho", "counterterm_p"])),
                encoding="utf-8",
            )
            matter_flux.write_text(json.dumps(_matter_flux_payload()), encoding="utf-8")

            payload = build_payload(
                cartan_path=cartan,
                holst_path=holst,
                counterterm_path=counterterm,
                matter_flux_path=matter_flux,
                partial_input_path=root / "partial.json",
                flrw_input_path=root / "flrw_inputs.json",
                flrw_manifest_path=flrw_manifest,
            )
            written = json.loads(flrw_manifest.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(payload["non_matter_inputs_passed"])
        self.assertTrue(payload["transparent_matter_flux_merge_passed"])
        self.assertTrue(payload["flrw_component_manifest_writer_passed"])
        self.assertTrue(payload["upstream_frontiers"]["non_matter"]["passed"])
        self.assertIn("matter_flux_rho", written["flrw_components_over_rho_crit0"])
        self.assertFalse(written["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()
