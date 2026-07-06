import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_surface_hk_radius_grid_from_rsigma_solution import (
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
        "observational_fit_used": False,
    }
    payload.update(fields)
    return payload


class SurfaceHKRadiusGridFromRSigmaSolutionTests(unittest.TestCase):
    def test_writes_radius_grid_from_minimal_rsigma_solution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "rsigma.json"
            output = root / "radius.json"
            source.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_of_a=[2.0, 3.0],
                        z2_orientation_sign=-1.0,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["round_throat_radius_grid_ready"])
        self.assertEqual(written["R_Sigma_values"], [2.0, 3.0])
        self.assertEqual(written["normal_orientation_sign"], -1.0)

    def test_missing_rsigma_solution_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "rsigma_radius_solution")


if __name__ == "__main__":
    unittest.main()
