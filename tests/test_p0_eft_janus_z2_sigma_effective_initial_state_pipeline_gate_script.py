import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import build_p0_eft_janus_z2_sigma_effective_initial_state_pipeline_gate as gate
from scripts.write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge import (
    build_payload as original_dimensionless_density,
)
from scripts.write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation import (
    build_payload as original_effective_closure,
)
from scripts.write_p0_eft_janus_z2_sigma_hubble_volume_noether_density import (
    build_payload as original_hubble_volume_density,
)
from scripts.write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state import (
    build_payload as original_projected_charge,
)


def _partial(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "derived_effective_initial_data": {
                    "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                }
            }
        ),
        encoding="utf-8",
    )


def _occupation(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "explicit_state_initial_data",
                "full_no_fit_prediction_ready": False,
                "N_occ_Z2Sigma": 2.0,
                "N_occ_provenance": "declared_superselection_state_initial_data",
            }
        ),
        encoding="utf-8",
    )


def _scale(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "scalars": {"h0_R_curv_over_c_Z2Sigma": 3.0},
            }
        ),
        encoding="utf-8",
    )


class EffectiveInitialStatePipelineGateTests(unittest.TestCase):
    def test_live_pipeline_blocks_without_occupation_manifest(self):
        payload = gate.build_payload()

        self.assertFalse(payload["pipeline_ready"])
        self.assertEqual(payload["primary_blocker"], "effective_closure")

    def test_pipeline_can_run_when_explicit_occupation_is_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            partial = root / "partial.json"
            occupation = root / "occupation.json"
            effective = root / "effective.json"
            source = root / "source.json"
            charge = root / "charge.json"
            density = root / "density.json"
            scale = root / "scale.json"
            hubble_density = root / "hubble_density.json"
            _partial(partial)
            _occupation(occupation)
            _scale(scale)

            def closure():
                return original_effective_closure(
                    partial_path=partial,
                    occupation_path=occupation,
                    output_path=effective,
                )

            def projected_charge():
                return original_projected_charge(
                    occupation_path=occupation,
                    source_path=source,
                    charge_path=charge,
                )

            def dimensionless_density():
                return original_dimensionless_density(
                    charge_path=charge,
                    output_path=density,
                )

            def hubble_volume_density():
                return original_hubble_volume_density(
                    density_path=density,
                    scale_path=scale,
                    output_path=hubble_density,
                )

            with patch.object(gate, "build_effective_closure", closure), patch.object(
                gate, "build_projected_charge", projected_charge
            ), patch.object(gate, "build_dimensionless_density", dimensionless_density), patch.object(
                gate, "build_hubble_volume_density", hubble_volume_density
            ):
                payload = gate.build_payload()

        self.assertTrue(payload["pipeline_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
