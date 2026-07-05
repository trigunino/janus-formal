import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate import (
    build_payload,
)


def _component_payload(fields, values=None, a_grid=None, provenance_suffix="derivation"):
    values = values or [0.1, 0.2, 0.3]
    a_grid = a_grid or [0.25, 0.5, 1.0]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid,
        "flrw_components_over_rho_crit0": {field: values for field in fields},
        "component_provenance": {field: f"active {field} {provenance_suffix}" for field in fields},
    }


class P0EFTJanusZ2SigmaFLRWNonMatterInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_component_manifests_block_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                cartan_path=Path(tmp) / "cartan.json",
                holst_path=Path(tmp) / "holst.json",
                counterterm_path=Path(tmp) / "counterterm.json",
                output_path=Path(tmp) / "partial.json",
            )

        self.assertFalse(payload["non_matter_flrw_inputs_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "cartan_holst_counterterm_components")
        self.assertIn("cartan_ghy_component", payload["upstream_frontiers"])
        self.assertIn("holst_nieh_yan_component", payload["upstream_frontiers"])
        self.assertIn("counterterm_component", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_non_matter_frontier"]["diagnostic_only"])
        self.assertIn(
            "cartan_ghy_component",
            payload["nearest_non_matter_frontier"]["blocks"],
        )
        cartan_inputs = payload["upstream_frontiers"]["cartan_ghy_component"][
            "required_inputs"
        ]
        self.assertEqual(cartan_inputs[0]["gate"], "janus-z2-sigma-cartan-ghy-deltaK-input-writer-gate")
        self.assertFalse(cartan_inputs[0]["exists"])
        self.assertIn(
            "derive_counterterm_radial_reduction",
            payload["upstream_frontiers"]["counterterm_component"]["next_required"],
        )

    def test_active_component_manifests_write_partial_flrw_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            cartan = Path(tmp) / "cartan.json"
            holst = Path(tmp) / "holst.json"
            counterterm = Path(tmp) / "counterterm.json"
            output = Path(tmp) / "partial.json"
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

            payload = build_payload(
                cartan_path=cartan,
                holst_path=holst,
                counterterm_path=counterterm,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("cartan_ghy_rho", written["flrw_components_over_rho_crit0"])
        self.assertIn("holst_nieh_yan_p", written["flrw_components_over_rho_crit0"])
        self.assertIn("counterterm_p", written["flrw_components_over_rho_crit0"])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_grid_mismatch_blocks_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            cartan = Path(tmp) / "cartan.json"
            holst = Path(tmp) / "holst.json"
            counterterm = Path(tmp) / "counterterm.json"
            output = Path(tmp) / "partial.json"
            cartan.write_text(
                json.dumps(_component_payload(["cartan_ghy_rho", "cartan_ghy_p"])),
                encoding="utf-8",
            )
            holst.write_text(
                json.dumps(
                    _component_payload(
                        ["holst_nieh_yan_rho", "holst_nieh_yan_p"], a_grid=[0.3, 0.5, 1.0]
                    )
                ),
                encoding="utf-8",
            )
            counterterm.write_text(
                json.dumps(_component_payload(["counterterm_rho", "counterterm_p"])),
                encoding="utf-8",
            )

            payload = build_payload(
                cartan_path=cartan,
                holst_path=holst,
                counterterm_path=counterterm,
                output_path=output,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("a_grids", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
