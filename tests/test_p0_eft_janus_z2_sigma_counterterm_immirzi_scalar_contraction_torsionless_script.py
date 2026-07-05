import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_immirzi_scalar_contraction_torsionless import (
    build_payload,
)


def _holst(**overrides):
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
        "torsionless_Nieh_Yan_zero_identity_ready": True,
        "holst_nieh_yan_radial_reduction_ready": True,
        "a_grid": [0.25, 0.5, 1.0],
        "E_HolstNiehYan_values": [0.0, 0.0, 0.0],
    }
    payload.update(overrides)
    return payload


class ImmirziScalarContractionTorsionlessTests(unittest.TestCase):
    def test_writes_zero_radial_contraction_without_solving_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holst = root / "holst.json"
            output = root / "immirzi.json"
            holst.write_text(json.dumps(_holst()), encoding="utf-8")

            payload = build_payload(holst_path=holst, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["R_chi_partial_R_chi_values"], [0.0, 0.0, 0.0])
        self.assertFalse(written["R_chi_profile_solved"])
        self.assertFalse(written["partial_R_chi_profile_solved"])
        self.assertFalse(written["L_ct_integration_constant_fixed"])

    def test_nonzero_holst_radial_term_blocks_zero_contraction(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holst = root / "holst.json"
            holst.write_text(
                json.dumps(_holst(E_HolstNiehYan_values=[0.0, 1.0, 0.0])),
                encoding="utf-8",
            )

            payload = build_payload(holst_path=holst, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("must vanish", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
