import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation import (
    build_payload,
)


def _partial(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "partial_effective_closure_from_projective_geometry",
                "full_no_fit_prediction_ready": False,
                "derived_effective_initial_data": {
                    "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                },
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
                "N_occ_Z2Sigma": 5.0,
                "N_occ_provenance": "declared_superselection_state_initial_data",
            }
        ),
        encoding="utf-8",
    )


class JanusZ2SigmaEffectiveClosureFromRatioAndOccupationScriptTest(unittest.TestCase):
    def test_missing_occupation_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial = Path(tmp) / "partial.json"
            output = Path(tmp) / "effective.json"
            _partial(partial)
            payload = build_payload(
                partial_path=partial,
                occupation_path=Path(tmp) / "missing.json",
                output_path=output,
            )

        self.assertFalse(payload["effective_closure_ready"])
        self.assertEqual(payload["primary_blocker"], "projected_occupation_state_inputs_json")

    def test_explicit_occupation_writes_effective_closure_without_no_fit_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial = Path(tmp) / "partial.json"
            occupation = Path(tmp) / "occupation.json"
            output = Path(tmp) / "effective.json"
            _partial(partial)
            _occupation(occupation)
            payload = build_payload(
                partial_path=partial,
                occupation_path=occupation,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["effective_closure_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(
            written["effective_initial_data"]["R_Sigma_over_ell_collar_Z2Sigma"],
            1.0,
        )
        self.assertEqual(
            written["effective_initial_data"]["projected_baryon_number_charge_Z2Sigma"],
            5.0,
        )

    def test_example_style_occupation_can_drive_writer_only_when_explicitly_passed(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial = Path(tmp) / "partial.json"
            occupation = Path(tmp) / "example_occupation.json"
            output = Path(tmp) / "effective.json"
            _partial(partial)
            occupation.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "explicit_state_initial_data",
                        "full_no_fit_prediction_ready": False,
                        "N_occ_Z2Sigma": 1.0,
                        "N_occ_provenance": "example_declared_superselection_state_initial_data_not_active",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                partial_path=partial,
                occupation_path=occupation,
                output_path=output,
            )

        self.assertTrue(payload["effective_closure_ready"])
        self.assertEqual(
            payload["effective_initial_data"][
                "projected_baryon_number_charge_Z2Sigma"
            ],
            1.0,
        )


if __name__ == "__main__":
    unittest.main()
