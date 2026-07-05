import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate import (
    build_payload as build_density_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_history_firas_codata_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    build_payload as build_temperature_payload,
)


class P0EFTJanusZ2SigmaPhotonDensityHistoryFIRASCODATAGateTests(unittest.TestCase):
    def test_missing_rho0_blocks_history(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "history.json",
            )
        self.assertFalse(payload["gate_passed"])

    def test_writes_conserved_photon_history(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            constants = root / "constants.json"
            temperature = root / "temperature.json"
            rho0 = root / "rho0.json"
            history = root / "history.json"
            build_constants_payload(output_path=constants)
            build_temperature_payload(output_path=temperature)
            build_density_payload(
                constants_path=constants,
                temperature_path=temperature,
                output_path=rho0,
            )
            payload = build_payload(
                input_path=rho0,
                output_path=history,
                z_grid=[0.0, 1.0],
            )
            written = json.loads(history.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        rho0_value = written["normalizations"]["rho_photon0_Z2Sigma_J_m3"]
        self.assertEqual(written["rho_photon_Z2Sigma_J_m3"][0], rho0_value)
        self.assertAlmostEqual(written["rho_photon_Z2Sigma_J_m3"][1], 16.0 * rho0_value)
        self.assertFalse(written["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()
