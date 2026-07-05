import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload,
)


def _charge_payload(*, projected_current_ready: bool = True) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_baryon_fit_used": False,
        "projected_Dirac_current_ready": projected_current_ready,
        "charge_boundary_projection_ready": True,
        "projection_weights_free": False,
        "normalizations": {
            "projected_baryon_number_charge_Z2Sigma": 7.0,
        },
        "normalization_provenance": {
            "projected_baryon_number_charge_Z2Sigma": "active_Dirac_boundary_projection",
        },
    }


class P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["requires_projected_Dirac_current"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertIn("dirac_charge_boundary_projection", payload["upstream_frontiers"])
        self.assertIn("dirac_number_normalization", payload["upstream_frontiers"])
        self.assertFalse(
            payload["upstream_frontiers"]["dirac_number_normalization"]["ready"]
        )
        self.assertIn(
            "active_Dirac_number_normalization",
            payload["nearest_projected_baryon_charge_frontier"]["blocks"],
        )
        self.assertTrue(payload["nearest_projected_baryon_charge_frontier"]["diagnostic_only"])
        self.assertIn("derive_projected_baryon_number_charge_Z2Sigma", payload["next_required"])

    def test_valid_active_source_writes_projected_charge(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "charge_source.json"
            output_path = tmpdir / "charge.json"
            input_path.write_text(json.dumps(_charge_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["projected_baryon_charge_manifest_written"])
        self.assertEqual(
            written["normalizations"]["projected_baryon_number_charge_Z2Sigma"],
            7.0,
        )
        self.assertFalse(payload["dirac_charge_boundary_projection_ready"])
        self.assertTrue(payload["input_active_derived_manifest_is_authoritative"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(payload["nearest_projected_baryon_charge_frontier"]["blocks"], [])

    def test_requires_projected_dirac_current(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "charge_source.json"
            input_path.write_text(
                json.dumps(_charge_payload(projected_current_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("projected_Dirac_current_ready", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
