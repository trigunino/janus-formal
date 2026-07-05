import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_active_inputs_to_scale_free_primitive_chi2_gate import (
    build_payload,
)
from tests.test_p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate_script import (
    _background_inputs,
    _early_inputs,
    _flrw_inputs,
)


class P0EFTJanusZ2SigmaActiveInputsToScaleFreePrimitiveChi2GateTests(unittest.TestCase):
    def test_missing_inputs_block_before_writing_intermediates(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_out = tmpdir / "background_scalars.json"
            payload = build_payload(
                background_input_path=tmpdir / "missing_background.json",
                flrw_input_path=tmpdir / "missing_flrw.json",
                early_input_path=tmpdir / "missing_early.json",
                background_manifest_path=background_out,
                flrw_manifest_path=tmpdir / "flrw_components.json",
                early_manifest_path=tmpdir / "early_plasma.json",
                component_manifest_path=tmpdir / "bao_component_inputs.json",
                background_primitive_path=tmpdir / "background_primitive.json",
                plasma_primitive_path=tmpdir / "plasma_primitive.json",
                primitive_input_path=tmpdir / "primitive.json",
                scale_free_input_path=tmpdir / "scale_free.json",
            )

            self.assertFalse(background_out.exists())

        self.assertFalse(payload["required_input_manifests_available"])
        self.assertFalse(payload["atomic_preflight_passed"])
        self.assertFalse(payload["primitive_chain_executed"])
        self.assertFalse(payload["gate_passed"])

    def test_strict_active_inputs_block_until_counterterm_is_derived(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background = tmpdir / "background_scalar_inputs.json"
            flrw = tmpdir / "flrw_component_inputs.json"
            early = tmpdir / "early_plasma_inputs.json"
            background.write_text(json.dumps(_background_inputs()), encoding="utf-8")
            flrw.write_text(json.dumps(_flrw_inputs()), encoding="utf-8")
            early.write_text(json.dumps(_early_inputs()), encoding="utf-8")

            payload = build_payload(
                background_input_path=background,
                flrw_input_path=flrw,
                early_input_path=early,
                background_manifest_path=tmpdir / "background_scalars.json",
                flrw_manifest_path=tmpdir / "flrw_components.json",
                early_manifest_path=tmpdir / "early_plasma.json",
                component_manifest_path=tmpdir / "bao_component_inputs.json",
                background_primitive_path=tmpdir / "background_primitive.json",
                plasma_primitive_path=tmpdir / "plasma_primitive.json",
                primitive_input_path=tmpdir / "primitive.json",
                scale_free_input_path=tmpdir / "scale_free.json",
            )

        self.assertTrue(payload["required_input_manifests_available"])
        self.assertFalse(payload["counterterm_radial_reduction_ready"])
        self.assertFalse(payload["atomic_preflight_passed"])
        self.assertFalse(payload["background_scalar_manifest_written"])
        self.assertFalse(payload["flrw_component_manifest_written"])
        self.assertFalse(payload["early_plasma_manifest_written"])
        self.assertFalse(payload["bao_component_manifest_written"])
        self.assertFalse(payload["primitive_chain_executed"])
        self.assertFalse(payload["primitive_inputs_assembler_passed"])
        self.assertFalse(payload["primitive_chi2_passed"])
        self.assertFalse(payload["bao_chi2_evaluated"])
        self.assertFalse(payload["Gamma_drag_over_H0_Z2Sigma_available"])
        self.assertFalse(payload["gate_passed"])
        self.assertIsNone(payload["chi2_DESI_DR2_BAO"])
        self.assertEqual(
            payload["blocker"],
            "counterterm density/rho_p not derived from active Sigma radial reduction",
        )


if __name__ == "__main__":
    unittest.main()
