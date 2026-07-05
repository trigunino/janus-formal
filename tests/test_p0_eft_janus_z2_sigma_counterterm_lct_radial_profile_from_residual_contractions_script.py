import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_lct_radial_profile_from_residual_contractions import (
    build_payload,
)


def _source(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "residual_scalar_contractions_ready": True,
        "a_grid": [0.5, 1.0, 1.5],
        "R_Sigma_values": [2.0, 3.0, 4.0],
        "R_h_q_contract_values": [1.0, 1.5, 2.0],
        "R_K_q_contract_values": [0.5, 0.25, 0.0],
        "R_chi_partial_R_chi_values": [0.0, 0.0, 0.0],
        "L_ct_integration_constant_fixed": True,
        "L_ct_reference_index": 0,
        "L_ct_reference_value": 10.0,
    }
    payload.update(overrides)
    return payload


class CountertermLctRadialProfileFromResidualContractionsTests(unittest.TestCase):
    def test_writes_lct_profile_from_scalar_contractions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "contractions.json"
            output_path = root / "profile.json"
            input_path.write_text(json.dumps(_source()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["L_ct_profile_ready"])
        self.assertEqual(written["partial_R_L_ct_values"], [-4.5, -9.25, -16.0])
        self.assertEqual(written["L_ct_values"], [10.0, 3.125, -9.5])

    def test_blocks_without_fixed_integration_constant(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "contractions.json"
            input_path.write_text(
                json.dumps(_source(L_ct_integration_constant_fixed=False)),
                encoding="utf-8",
            )

            payload = build_payload(
                input_path=input_path,
                output_path=root / "profile.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("L_ct_integration_constant_fixed", payload["validation_error"])

    def test_missing_contractions_reports_next_physical_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "profile.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "counterterm_residual_scalar_contractions_inputs",
        )
        self.assertIn("derive_R_h_ab_q_ab_from_active_boundary_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
