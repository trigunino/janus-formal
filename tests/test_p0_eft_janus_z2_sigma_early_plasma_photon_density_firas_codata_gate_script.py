import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    RADIATION_CONSTANT_SI,
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    T_CMB_FIRAS_K,
    build_payload as build_temperature_payload,
)


class P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityFIRASCODATAGateTests(unittest.TestCase):
    def test_missing_upstream_manifests_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                constants_path=Path(tmp) / "constants.json",
                temperature_path=Path(tmp) / "temperature.json",
                output_path=Path(tmp) / "rho.json",
            )
        self.assertFalse(payload["gate_passed"])

    def test_writes_photon_density_from_firas_and_codata(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            constants = root / "constants.json"
            temperature = root / "temperature.json"
            output = root / "rho.json"
            build_constants_payload(output_path=constants)
            build_temperature_payload(output_path=temperature)
            payload = build_payload(
                constants_path=constants,
                temperature_path=temperature,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(
            written["normalizations"]["rho_photon0_Z2Sigma_J_m3"],
            RADIATION_CONSTANT_SI * T_CMB_FIRAS_K**4,
        )
        self.assertFalse(written["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()
