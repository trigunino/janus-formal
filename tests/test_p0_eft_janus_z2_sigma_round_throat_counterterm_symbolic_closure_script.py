import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_round_throat_counterterm_symbolic_closure import (
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


class RoundThroatCountertermSymbolicClosureScriptTests(unittest.TestCase):
    def test_writes_values_when_coefficients_and_radius_exist(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            coeff = root / "coeff.json"
            radius = root / "radius.json"
            output = root / "out.json"
            coeff.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5],
                        a0_values=[1.0],
                        a1_values=[2.0],
                        a2_values=[3.0],
                        a3_values=[4.0],
                    )
                ),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5],
                        R_Sigma_values=[2.0],
                        normal_orientation_sign=-1.0,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(coeff_path=coeff, radius_path=radius, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["symbolic_closure_ready"])
        self.assertTrue(written["values_written"])
        self.assertEqual(written["values"]["E_counterterm_values"], [27.0])

    def test_symbolic_closure_ready_without_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                coeff_path=Path(tmp) / "missing_coeff.json",
                radius_path=Path(tmp) / "missing_radius.json",
                output_path=Path(tmp) / "out.json",
            )

        self.assertTrue(payload["symbolic_closure_ready"])
        self.assertFalse(payload["values_written"])


if __name__ == "__main__":
    unittest.main()
