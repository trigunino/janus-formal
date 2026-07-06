import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate import (
    build_payload,
)


def _normal_current_ready():
    return {
        "no_normal_matter_current_ready": True,
        "closure": {"no_normal_matter_current_derived": True},
    }


def _bulk_stress_ready():
    return {
        "bulk_stress_normal_flux_projection_ready": True,
        "bulk_stress_normal_flux_cancellation_ready": True,
        "closure": {
            "Z2_flux_cancellation_derived": True,
            "bulk_stress_normal_projection_zero_derived": False,
        }
    }


def _grid_source():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.25, 0.5, 1.0],
    }


def _perfect_fluid_flux_ready():
    return {"perfect_fluid_tangential_flux_zero_ready": True, "gate_passed": True}


def _holst_flux_ready():
    return {"holst_torsion_flux_zero_or_equivariance_ready": True, "gate_passed": True}


class P0EFTJanusZ2SigmaMatterFluxTransparencyInputWriterGateTests(unittest.TestCase):
    def test_default_gate_blocks_without_inputs_and_closure(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                grid_source_path=Path(tmp) / "missing.json",
                grid_fallback_path=Path(tmp) / "missing_fallback.json",
                output_path=Path(tmp) / "transparency.json",
            )

        self.assertFalse(payload["grid_source_exists"])
        self.assertFalse(payload["grid_fallback_exists"])
        self.assertTrue(payload["active_sigma_transparency_derived"])
        self.assertEqual(payload["transparency_scope"], "local_Sigma_flux_slot")
        self.assertFalse(payload["transparency_input_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("normal_matter_current", payload["upstream_frontiers"])
        self.assertIn("bulk_stress_normal_flux", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_transparency_input_frontier"]["diagnostic_only"])

    def test_ready_current_and_bulk_flux_write_transparency_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            grid_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "transparency.json"
            grid_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=grid_path,
                output_path=output_path,
                normal_current_payload=_normal_current_ready(),
                bulk_stress_payload=_bulk_stress_ready(),
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["active_sigma_transparency_derived"])
        self.assertEqual(written["a_grid"], [0.25, 0.5, 1.0])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_missing_bulk_flux_closure_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            grid_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "transparency.json"
            grid_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=grid_path,
                output_path=output_path,
                normal_current_payload=_normal_current_ready(),
                bulk_stress_payload={
                    "closure": {
                        "Z2_flux_cancellation_derived": False,
                        "bulk_stress_normal_projection_zero_derived": False,
                    }
                },
                perfect_fluid_flux_payload={"perfect_fluid_tangential_flux_zero_ready": False},
                holst_flux_payload={"holst_torsion_flux_zero_or_equivariance_ready": False},
            )

        self.assertFalse(payload["active_sigma_transparency_derived"])
        self.assertFalse(payload["gate_passed"])

    def test_flux_closure_without_projection_readiness_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            grid_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "transparency.json"
            grid_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=grid_path,
                output_path=output_path,
                normal_current_payload=_normal_current_ready(),
                bulk_stress_payload={
                    "bulk_stress_normal_flux_projection_ready": False,
                    "bulk_stress_normal_flux_cancellation_ready": True,
                    "closure": {
                        "Z2_flux_cancellation_derived": True,
                        "bulk_stress_normal_projection_zero_derived": False,
                    },
                },
                perfect_fluid_flux_payload={"perfect_fluid_tangential_flux_zero_ready": False},
                holst_flux_payload={"holst_torsion_flux_zero_or_equivariance_ready": False},
            )

        self.assertFalse(payload["bulk_stress_projection_ready"])
        self.assertFalse(payload["active_sigma_transparency_derived"])
        self.assertFalse(payload["gate_passed"])

    def test_local_sigma_flux_slot_route_writes_transparency_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            grid_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "transparency.json"
            grid_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=grid_path,
                output_path=output_path,
                normal_current_payload={"closure": {"no_normal_matter_current_derived": False}},
                bulk_stress_payload={
                    "closure": {
                        "Z2_flux_cancellation_derived": False,
                        "bulk_stress_normal_projection_zero_derived": False,
                    }
                },
                perfect_fluid_flux_payload=_perfect_fluid_flux_ready(),
                holst_flux_payload=_holst_flux_ready(),
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["local_sigma_flux_slot_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["transparency_scope"], "local_Sigma_flux_slot")
        self.assertEqual(written["transparency_scope"], "local_Sigma_flux_slot")

    def test_local_sigma_flux_slot_requires_holst_flux_closure(self):
        with tempfile.TemporaryDirectory() as tmp:
            grid_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "transparency.json"
            grid_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=grid_path,
                output_path=output_path,
                normal_current_payload={"closure": {"no_normal_matter_current_derived": False}},
                bulk_stress_payload={
                    "closure": {
                        "Z2_flux_cancellation_derived": False,
                        "bulk_stress_normal_projection_zero_derived": False,
                    }
                },
                perfect_fluid_flux_payload=_perfect_fluid_flux_ready(),
                holst_flux_payload={
                    "holst_torsion_flux_zero_or_equivariance_ready": False,
                    "gate_passed": False,
                },
            )

        self.assertFalse(payload["local_sigma_flux_slot_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_holst_component_grid_fallback_writes_transparency_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            fallback_path = Path(tmp) / "holst_components.json"
            output_path = Path(tmp) / "transparency.json"
            fallback_path.write_text(json.dumps(_grid_source()), encoding="utf-8")

            payload = build_payload(
                grid_source_path=Path(tmp) / "missing.json",
                grid_fallback_path=fallback_path,
                output_path=output_path,
                normal_current_payload={"closure": {"no_normal_matter_current_derived": False}},
                bulk_stress_payload={
                    "closure": {
                        "Z2_flux_cancellation_derived": False,
                        "bulk_stress_normal_projection_zero_derived": False,
                    }
                },
                perfect_fluid_flux_payload=_perfect_fluid_flux_ready(),
                holst_flux_payload=_holst_flux_ready(),
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertFalse(payload["grid_source_exists"])
        self.assertTrue(payload["grid_fallback_exists"])
        self.assertTrue(payload["selected_grid_source_exists"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["a_grid"], [0.25, 0.5, 1.0])


if __name__ == "__main__":
    unittest.main()
