import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_baryon_density_si_from_dimensionless_invariants import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_payload,
)


class BaryonDensitySIFromDimensionlessInvariantsScriptTest(unittest.TestCase):
    def test_missing_scale_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                r3_density_path=root / "density.json",
                hubble_density_path=root / "hubble.json",
                r_curv_path=root / "r.json",
                h0_path=root / "h0.json",
                output_path=root / "out.json",
            )

            self.assertFalse(payload["gate_passed"])
            self.assertEqual(payload["primary_blocker"], "H0_Z2Sigma_or_R_curv_Z2Sigma_m")

    def test_r_curv_route_writes_density(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            radius = root / "radius.json"
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
            radius.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scalars": {"R_curv_Z2Sigma_Mpc": 2.0 / 3.0856775814913673e22},
                        "scalar_provenance": {"R_curv_Z2Sigma": "active_radius"},
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                r3_density_path=density,
                r_curv_path=radius,
                hubble_density_path=root / "missing_hubble.json",
                h0_path=root / "missing_h0.json",
                output_path=output,
            )

            self.assertTrue(payload["gate_passed"])
            written = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(written["normalization_route"], "R_curv")
            self.assertAlmostEqual(
                written["normalizations"]["baryon_number_density0_m3_Z2Sigma"],
                1.0,
            )

    def test_written_density_feeds_saha_history(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            density = root / "density.json"
            radius = root / "radius.json"
            baryon = root / "baryon.json"
            temperature = root / "temperature.json"
            constants = root / "constants.json"
            history = root / "history.json"
            density.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "dimensionless_density": {
                            "baryon_number_density0_times_Rcurv3_Z2Sigma": 8.0e9,
                        },
                    }
                ),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scalars": {"R_curv_Z2Sigma_Mpc": 2.0 / 3.0856775814913673e22},
                        "scalar_provenance": {"R_curv_Z2Sigma": "active_radius"},
                    }
                ),
                encoding="utf-8",
            )
            temperature.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "direct_noncompressed_observation",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "normalizations": {"photon_temperature0_Z2Sigma": 2.7255},
                    }
                ),
                encoding="utf-8",
            )
            build_constants_payload(output_path=constants)

            density_payload = build_payload(
                r3_density_path=density,
                r_curv_path=radius,
                hubble_density_path=root / "missing_hubble.json",
                h0_path=root / "missing_h0.json",
                output_path=baryon,
            )
            saha_payload = build_saha_payload(
                baryon_input_path=baryon,
                temperature_input_path=temperature,
                constants_input_path=constants,
                output_path=history,
            )

            self.assertTrue(density_payload["gate_passed"])
            self.assertTrue(saha_payload["gate_passed"])
            self.assertTrue(history.exists())


if __name__ == "__main__":
    unittest.main()
