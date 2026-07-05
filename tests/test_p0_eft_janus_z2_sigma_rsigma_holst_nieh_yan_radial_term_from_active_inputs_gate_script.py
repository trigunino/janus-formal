import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate import (
    build_payload,
)


def _holst_input(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "torsion_pullback_on_Sigma_ready": True,
        "FLRW_irreducible_torsion_pullback_ready": True,
        "Immirzi_radial_profile_ready": True,
        "holst_nieh_yan_radial_reduction_ready": True,
        "selected_radial_term": "E_HolstNiehYan",
        "a_grid": [0.25, 0.5, 1.0],
        "E_HolstNiehYan_values": [0.1, -0.2, 0.3],
    }
    payload.update(overrides)
    return payload


class RSigmaHolstNiehYanRadialTermFromActiveInputsGateTests(unittest.TestCase):
    def test_writes_radial_term_from_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "holst.json"
            output = root / "out.json"
            source.write_text(json.dumps(_holst_input()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["E_HolstNiehYan_from_active_inputs_written"])
        self.assertEqual(written["term_name"], "E_HolstNiehYan")
        self.assertEqual(written["term_values"], [0.1, -0.2, 0.3])

    def test_blocks_without_torsion_pullback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "holst.json"
            source.write_text(
                json.dumps(_holst_input(torsion_pullback_on_Sigma_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("torsion_pullback_on_Sigma_ready", payload["validation_error"])

    def test_blocks_without_immirzi_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "holst.json"
            source.write_text(
                json.dumps(_holst_input(Immirzi_radial_profile_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Immirzi_radial_profile_ready", payload["validation_error"])

    def test_blocks_wrong_radial_term_route(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "holst.json"
            source.write_text(
                json.dumps(_holst_input(selected_radial_term="E_counterterm")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("selected_radial_term", payload["validation_error"])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "holst.json"
            source.write_text(
                json.dumps(_holst_input(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
