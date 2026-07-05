import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_geometry_factors_from_unit_q_gate import (
    build_payload,
)


def _q(**overrides):
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
        "unit_intrinsic_metric_q_ab": [
            [1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0],
            [0.0, 0.0, 1.0],
        ],
    }
    payload.update(overrides)
    return payload


class CountertermRadialGeometryFactorsFromUnitQGateTests(unittest.TestCase):
    def test_derives_sqrt_h_formulas_from_unit_q(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            out_path = root / "out.json"
            q_path.write_text(json.dumps(_q()), encoding="utf-8")

            payload = build_payload(q_input_path=q_path, output_path=out_path)
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["dimension"], 3)
        self.assertEqual(written["sqrt_det_unit_q"], 1.0)
        self.assertEqual(written["sqrt_abs_h_formula"], "sqrt_abs_h(R) = R_Sigma^3 * sqrt_det_unit_q")
        self.assertEqual(
            written["partial_R_sqrt_abs_h_formula"],
            "partial_R_sqrt_abs_h(R) = 3 * R_Sigma^2 * sqrt_det_unit_q",
        )
        self.assertTrue(written["requires_R_Sigma_of_a_for_values"])

    def test_forbidden_fit_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            q_path.write_text(
                json.dumps(_q(fitted_counterterm_coefficient_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(q_input_path=q_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
