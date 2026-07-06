import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_inputs_merge_transparent_matter_flux_gate import (
    build_payload,
)


def _partial_payload():
    a_grid = [0.25, 0.5, 1.0]
    fields = [
        "cartan_ghy_rho",
        "cartan_ghy_p",
        "holst_nieh_yan_rho",
        "holst_nieh_yan_p",
        "counterterm_rho",
        "counterterm_p",
    ]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid,
        "flrw_components_over_rho_crit0": {field: [0.1, 0.2, 0.3] for field in fields},
        "component_provenance": {field: f"active {field} derivation" for field in fields},
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


class P0EFTJanusZ2SigmaFLRWInputsMergeTransparentMatterFluxGateTests(unittest.TestCase):
    def test_missing_inputs_block_merge(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                partial_input_path=Path(tmp) / "partial.json",
                matter_flux_path=Path(tmp) / "matter.json",
                output_path=Path(tmp) / "out.json",
                auto_write_matter_flux=False,
            )

        self.assertFalse(payload["partial_input_exists"])
        self.assertFalse(payload["matter_flux_component_exists"])
        self.assertFalse(payload["merged_flrw_component_inputs_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "non_matter_inputs_and_transparent_matter_flux")
        self.assertIn("zero_matter_flux_component", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_matter_flux_merge_frontier"]["diagnostic_only"])

    def test_merge_writes_complete_flrw_component_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial_path = Path(tmp) / "partial.json"
            matter_path = Path(tmp) / "matter.json"
            output_path = Path(tmp) / "flrw_component_inputs.json"
            partial_path.write_text(json.dumps(_partial_payload()), encoding="utf-8")
            matter_path.write_text(json.dumps(_matter_flux_payload()), encoding="utf-8")

            payload = build_payload(
                partial_input_path=partial_path,
                matter_flux_path=matter_path,
                output_path=output_path,
                auto_write_matter_flux=False,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["flrw_components_over_rho_crit0"]["matter_flux_rho"], [0.0, 0.0, 0.0])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["matter_flux_p"], [0.0, 0.0, 0.0])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_grid_mismatch_blocks_merge(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial_path = Path(tmp) / "partial.json"
            matter_path = Path(tmp) / "matter.json"
            output_path = Path(tmp) / "flrw_component_inputs.json"
            matter = _matter_flux_payload()
            matter["a_grid"] = [0.2, 0.5, 1.0]
            partial_path.write_text(json.dumps(_partial_payload()), encoding="utf-8")
            matter_path.write_text(json.dumps(matter), encoding="utf-8")

            payload = build_payload(
                partial_input_path=partial_path,
                matter_flux_path=matter_path,
                output_path=output_path,
                auto_write_matter_flux=False,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("a_grid", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
