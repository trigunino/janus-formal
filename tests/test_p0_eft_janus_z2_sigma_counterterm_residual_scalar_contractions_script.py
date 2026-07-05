import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_scalar_contractions import (
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


class CountertermResidualScalarContractionsTests(unittest.TestCase):
    def test_writes_scalar_contractions_from_tensors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q = root / "q.json"
            radius = root / "radius.json"
            metric = root / "metric.json"
            extrinsic = root / "extrinsic.json"
            immirzi = root / "immirzi.json"
            output = root / "out.json"
            q.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 2.0]])),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(_active(a_grid=[0.5, 1.0], R_Sigma_values=[2.0, 3.0])),
                encoding="utf-8",
            )
            metric.write_text(
                json.dumps(_active(R_h_ab=[[[1.0, 0.0], [0.0, 3.0]], [[2.0, 0.0], [0.0, 4.0]]])),
                encoding="utf-8",
            )
            extrinsic.write_text(
                json.dumps(_active(R_K_ab=[[5.0, 0.0], [0.0, 7.0]])),
                encoding="utf-8",
            )
            immirzi.write_text(
                json.dumps(
                    _active(
                        R_chi_values=[11.0, 13.0],
                        partial_R_chi_values=[0.5, 0.25],
                        L_ct_integration_constant_fixed=True,
                        L_ct_reference_value=19.0,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                q_path=q,
                radius_path=radius,
                metric_path=metric,
                extrinsic_path=extrinsic,
                immirzi_path=immirzi,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["residual_scalar_contractions_ready"])
        self.assertEqual(written["R_h_q_contract_values"], [7.0, 10.0])
        self.assertEqual(written["R_K_q_contract_values"], [19.0, 19.0])
        self.assertEqual(written["R_chi_partial_R_chi_values"], [5.5, 3.25])
        self.assertTrue(written["L_ct_integration_constant_fixed"])
        self.assertEqual(written["L_ct_reference_value"], 19.0)

    def test_missing_radius_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                q_path=root / "missing_q.json",
                radius_path=root / "missing_radius.json",
                metric_path=root / "missing_metric.json",
                extrinsic_path=root / "missing_extrinsic.json",
                immirzi_path=root / "missing_immirzi.json",
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("unit_intrinsic_metric_q_ab", payload["next_required"])
        self.assertIn("R_Sigma_solution_certificate", payload["next_required"])

    def test_accepts_active_radius_certificate_key(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q = root / "q.json"
            radius = root / "radius.json"
            metric = root / "metric.json"
            extrinsic = root / "extrinsic.json"
            immirzi = root / "immirzi.json"
            output = root / "out.json"
            q.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(_active(a_grid=[0.5, 1.0], R_Sigma_of_a=[2.0, 3.0])),
                encoding="utf-8",
            )
            metric.write_text(json.dumps(_active(R_h_ab=[[1.0, 0.0], [0.0, 1.0]])), encoding="utf-8")
            extrinsic.write_text(json.dumps(_active(R_K_ab=[[2.0, 0.0], [0.0, 2.0]])), encoding="utf-8")
            immirzi.write_text(json.dumps(_active(R_chi_partial_R_chi_values=[0.0, 0.0])), encoding="utf-8")

            payload = build_payload(
                q_path=q,
                radius_path=radius,
                metric_path=metric,
                extrinsic_path=extrinsic,
                immirzi_path=immirzi,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_Sigma_values"], [2.0, 3.0])


if __name__ == "__main__":
    unittest.main()
