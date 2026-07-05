import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate import (
    build_payload,
)


def _active_payload(normalizations: dict, provenance: dict) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "normalizations": normalizations,
        "normalization_provenance": provenance,
    }


class P0EFTJanusZ2SigmaBaryonNumberDensityNoetherVolumeGateTests(unittest.TestCase):
    def test_gate_is_red_without_projected_charge_and_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                charge_path=root / "missing_charge.json",
                volume_path=root / "missing_volume.json",
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertFalse(payload["baryon_number_density0_ready"])
        self.assertIn("projected_baryon_charge", payload["upstream_frontiers"])
        self.assertIn("spatial_volume", payload["upstream_frontiers"])
        self.assertIn(
            "projected_baryon_charge",
            payload["nearest_baryon_density_frontier"]["blocks"],
        )
        self.assertIn(
            "spatial_volume",
            payload["nearest_baryon_density_frontier"]["blocks"],
        )
        self.assertIn("derive_projected_Noether_baryon_charge_Z2Sigma", payload["next_required"])
        self.assertIn("derive_active_spatial_volume0_Z2Sigma", payload["next_required"])

    def test_fixture_charge_and_volume_write_density_without_default_path_coupling(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            charge_path = root / "charge.json"
            volume_path = root / "volume.json"
            output_path = root / "out.json"
            charge_path.write_text(
                json.dumps(
                    {
                        **_active_payload(
                        {"projected_baryon_number_charge_Z2Sigma": 12.0},
                        {"projected_baryon_number_charge_Z2Sigma": "active_noether_charge"},
                        ),
                        "observational_baryon_fit_used": False,
                    }
                ),
                encoding="utf-8",
            )
            volume = _active_payload(
                {"spatial_volume0_m3_Z2Sigma": 3.0},
                {"spatial_volume0_m3_Z2Sigma": "active_projective_volume"},
            )
            volume["volume_policy"] = {
                "volume_convention": "projected_proper_volume",
                "z2_cover_factor_applied_once": True,
            }
            volume_path.write_text(json.dumps(volume), encoding="utf-8")

            payload = build_payload(
                charge_path=charge_path,
                volume_path=volume_path,
                output_path=output_path,
            )
            density = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(payload["accepts_explicit_active_manifests"])
        self.assertTrue(payload["active_projected_baryon_charge_valid"])
        self.assertTrue(payload["active_spatial_volume_valid"])
        self.assertEqual(payload["nearest_baryon_density_frontier"]["blocks"], [
            "validated_projected_baryon_charge_manifest",
            "validated_spatial_volume_manifest",
        ])
        self.assertEqual(
            density["normalizations"]["baryon_number_density0_m3_Z2Sigma"],
            4.0,
        )
        self.assertFalse(payload["projected_baryon_charge_gate_passed"])
        self.assertIsNone(payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
