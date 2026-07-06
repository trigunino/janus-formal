import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_profile_from_minimal_coefficients_gate import (
    build_payload,
)


def _active(**fields):
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
    }
    payload.update(fields)
    return payload


class CountertermLctProfileFromMinimalCoefficientsGateTests(unittest.TestCase):
    def test_writes_profile_from_coefficients(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            coeff = root / "coeff.json"
            output = root / "profile.json"
            coeff.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_values=[1.0, 2.0],
                        c1_values=[1.0, 1.0],
                        c2_values=[2.0, 2.0],
                        c3_values=[3.0, 3.0],
                        z2_orientation_sign=1.0,
                        coefficient_status="constant",
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(coeff_path=coeff, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["L_ct_profile_ready"])
        self.assertEqual(written["L_ct_values"][0], 3.0 + 18.0 + 18.0)
        self.assertEqual(written["partial_R_L_ct_values"][0], -3.0 - 36.0 - 36.0)
        self.assertEqual(
            written["partial_R_L_ct_convention"],
            "coefficient_values_held_fixed_under_local_radial_variation",
        )

    def test_missing_coefficients_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(coeff_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "counterterm_minimal_basis_coefficients")


if __name__ == "__main__":
    unittest.main()
