import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import run_p0_eft_janus_z2_sigma_effective_state_density_chain as chain
from scripts.write_p0_eft_janus_z2_sigma_hubble_volume_noether_density import (
    build_payload as build_hubble_density_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge import (
    build_payload as build_dimensionless_density_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state import (
    build_payload as build_charge_payload,
)


def _occupation_payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "explicit_state_initial_data",
        "full_no_fit_prediction_ready": False,
        "N_occ_Z2Sigma": 2.0,
        "N_occ_provenance": "declared_superselection_state_initial_data",
    }


class EffectiveStateDensityChainScriptTest(unittest.TestCase):
    def test_live_chain_shape_reports_blocker(self):
        payload = chain.build_payload()
        self.assertIn("chain_passed", payload)
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_chain_components_pass_with_temp_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            occupation = root / "occupation.json"
            source = root / "source.json"
            charge = root / "charge.json"
            density = root / "density.json"
            scale = root / "scale.json"
            hubble = root / "hubble.json"
            occupation.write_text(json.dumps(_occupation_payload()), encoding="utf-8")
            scale.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "scalars": {"h0_R_curv_over_c_Z2Sigma": 2.0},
                    }
                ),
                encoding="utf-8",
            )

            charge_payload = build_charge_payload(
                occupation_path=occupation,
                source_path=source,
                charge_path=charge,
            )
            density_payload = build_dimensionless_density_payload(
                charge_path=charge,
                output_path=density,
            )
            hubble_payload = build_hubble_density_payload(
                density_path=density,
                scale_path=scale,
                output_path=hubble,
            )

            self.assertTrue(charge_payload["gate_passed"])
            self.assertTrue(density_payload["gate_passed"])
            self.assertTrue(hubble_payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
