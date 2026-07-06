import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_hubble_volume_noether_density import (
    build_payload,
)


class HubbleVolumeNoetherDensityScriptTest(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                density_path=root / "density.json",
                scale_path=root / "scale.json",
                output_path=root / "out.json",
            )

            self.assertFalse(payload["gate_passed"])
            self.assertFalse((root / "out.json").exists())

    def test_valid_inputs_write_hubble_volume_density(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            scale = root / "scale.json"
            output = root / "out.json"
            density.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "dimensionless_density": {
                            "baryon_number_density0_times_Rcurv3_Z2Sigma": 8.0,
                        },
                    }
                ),
                encoding="utf-8",
            )
            scale.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scalars": {"h0_R_curv_over_c_Z2Sigma": 2.0},
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(density_path=density, scale_path=scale, output_path=output)

            self.assertTrue(payload["gate_passed"])
            written = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(
                written["dimensionless_density"][
                    "baryon_number_density0_times_Hubble_volume_Z2Sigma"
                ],
                1.0,
            )


if __name__ == "__main__":
    unittest.main()
