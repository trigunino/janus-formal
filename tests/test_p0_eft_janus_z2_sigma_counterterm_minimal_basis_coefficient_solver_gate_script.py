import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_coefficient_solver_gate import (
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


class CountertermMinimalBasisCoefficientSolverGateTests(unittest.TestCase):
    def test_solves_known_constant_coefficients_from_trace_targets(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            trace_path = root / "trace.json"
            q_path = root / "q.json"
            output_path = root / "coeffs.json"
            radius = [1.0, 2.0]
            eps = 1.0
            c1, c2, c3 = 0.2, -0.3, 0.4
            kappa = 10.0
            r_k = [
                -3.0 * eps * c1 / R**2 - 18.0 * c2 / R**3
                for R in radius
            ]
            r_h = [
                3.0 * eps * c1 / R + (18.0 * c2 + 6.0 * c3) / R**2
                for R in radius
            ]
            noncartan = [
                -(6.0 * eps * R / kappa + 6.0 * eps * c1 * R + 9.0 * c2 + 6.0 * c3)
                for R in radius
            ]
            trace_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_values=radius,
                        R_h_trace_values=r_h,
                        R_K_trace_values=r_k,
                        E_noncartan_values=noncartan,
                        z2_orientation_sign=eps,
                        linear_K_partition_closed=False,
                    )
                ),
                encoding="utf-8",
            )
            q_path.write_text(
                json.dumps(
                    _active(
                        unit_intrinsic_metric_q_ab=[
                            [1.0, 0.0, 0.0],
                            [0.0, 1.0, 0.0],
                            [0.0, 0.0, 1.0],
                        ],
                        kappa_Z2Sigma=kappa,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                trace_path=trace_path,
                q_path=q_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["constant_coefficients_consistent"])
        self.assertAlmostEqual(written["c1_values"][0], c1)
        self.assertAlmostEqual(written["c2_values"][0], c2)
        self.assertAlmostEqual(written["c3_values"][0], c3)
        self.assertLess(written["linear_system_residual_max_abs"], 1.0e-12)
        self.assertFalse(written["linear_K_partition_enforced"])

    def test_partitioned_solver_enforces_c1_zero(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            trace_path = root / "trace.json"
            q_path = root / "q.json"
            output_path = root / "coeffs.json"
            radius = [1.0, 2.0]
            c2, c3 = -0.3, 0.4
            kappa = 10.0
            r_k = [-18.0 * c2 / R**3 for R in radius]
            r_h = [(18.0 * c2 + 6.0 * c3) / R**2 for R in radius]
            noncartan = [
                -(6.0 * R / kappa + 9.0 * c2 + 6.0 * c3)
                for R in radius
            ]
            trace_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_values=radius,
                        R_h_trace_values=r_h,
                        R_K_trace_values=r_k,
                        E_noncartan_values=noncartan,
                        z2_orientation_sign=1.0,
                        linear_K_partition_closed=True,
                    )
                ),
                encoding="utf-8",
            )
            q_path.write_text(
                json.dumps(
                    _active(
                        unit_intrinsic_metric_q_ab=[
                            [1.0, 0.0, 0.0],
                            [0.0, 1.0, 0.0],
                            [0.0, 0.0, 1.0],
                        ],
                        kappa_Z2Sigma=kappa,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                trace_path=trace_path,
                q_path=q_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["linear_K_partition_enforced"])
        self.assertTrue(written["c1_zero_after_partition"])
        self.assertAlmostEqual(written["c1_values"][0], 0.0)
        self.assertLess(written["linear_system_residual_max_abs"], 1.0e-12)

    def test_missing_trace_inputs_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(trace_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("write_counterterm_trace_residual_inputs_json", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
