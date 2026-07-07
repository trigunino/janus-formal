import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_matter_state_from_noether_baryon_volume_gate import (
    build_payload,
)


class GlobalMatterStateFromNoetherBaryonVolumeGateTests(unittest.TestCase):
    def test_blocks_without_noether_density_and_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                baryon_density_path=base / "density.json",
                constants_path=base / "constants.json",
                volume_path=base / "volume.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["global_matter_state_ready"])
        self.assertIn(
            "missing_baryon_number_density_noether_volume_inputs",
            payload["validation_errors"],
        )

    def test_builds_global_matter_state_from_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            density = base / "density.json"
            constants = base / "constants.json"
            volume = base / "volume.json"
            density.write_text(
                """{
  "active_core": "Z2_tunnel_Sigma",
  "source": "active_derived",
  "compressed_planck_lcdm_rd_used": false,
  "archived_z4_reuse_used": false,
  "phenomenological_holst_bao_scan_used": false,
  "normalizations": {"baryon_number_density0_m3_Z2Sigma": 2.0}
}""",
                encoding="utf-8",
            )
            constants.write_text(
                """{
  "active_core": "Z2_tunnel_Sigma",
  "normalizations": {"baryon_mass_kg": 3.0}
}""",
                encoding="utf-8",
            )
            volume.write_text(
                """{
  "active_core": "Z2_tunnel_Sigma",
  "source": "active_derived",
  "compressed_planck_lcdm_rd_used": false,
  "archived_z4_reuse_used": false,
  "phenomenological_holst_bao_scan_used": false,
  "normalizations": {"spatial_volume0_m3_Z2Sigma": 5.0}
}""",
                encoding="utf-8",
            )
            payload = build_payload(
                baryon_density_path=density,
                constants_path=constants,
                volume_path=volume,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["matter_payload"]["rho_plus_kg_m3"], 6.0)
        self.assertEqual(payload["matter_payload"]["M_plus_kg"], 30.0)


if __name__ == "__main__":
    unittest.main()
