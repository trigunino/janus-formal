import json
import tempfile
import unittest
from pathlib import Path

from scripts.run_p0_eft_janus_z2_sigma_counterterm_chain import build_payload


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


class JanusZ2SigmaCountertermChainScriptTests(unittest.TestCase):
    def test_missing_inputs_report_first_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(base=Path(tmp) / "sigma")

        self.assertFalse(payload["chain_passed"])
        self.assertEqual(payload["first_blocker"], "active_unit_intrinsic_metric_q_ab_inputs")
        self.assertTrue(payload["circular_dependency"]["detected"])

    def test_chain_reaches_lct_boundary_constant_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "sigma"
            base.mkdir()
            (base / "unit_intrinsic_metric_q_ab_inputs.json").write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            (base / "holst_nieh_yan_radial_inputs.json").write_text(
                json.dumps(
                    _active(
                        torsionless_Nieh_Yan_zero_identity_ready=True,
                        holst_nieh_yan_radial_reduction_ready=True,
                        a_grid=[0.5, 1.0],
                        E_HolstNiehYan_values=[0.0, 0.0],
                    )
                ),
                encoding="utf-8",
            )
            (base / "counterterm_alpha_res_radial_components.json").write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_values=[2.0, 3.0],
                        sqrt_abs_h_values=[4.0, 9.0],
                        alpha_h_radial_coefficient_values=[8.0, 18.0],
                        alpha_K_radial_coefficient_values=[12.0, 27.0],
                    )
                ),
                encoding="utf-8",
            )
            (base / "rsigma_radius_solution.json").write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_of_a=[2.0, 3.0],
                        z2_orientation_sign=-1.0,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(base=base)
            scalar_contractions_written = (
                base / "counterterm_residual_scalar_contractions_inputs.json"
            ).exists()

        self.assertFalse(payload["chain_passed"])
        self.assertEqual(payload["first_blocker"], "L_ct_integration_constant_fixed must be true")
        self.assertTrue(scalar_contractions_written)
        self.assertFalse(payload["circular_dependency"]["detected"])


if __name__ == "__main__":
    unittest.main()
