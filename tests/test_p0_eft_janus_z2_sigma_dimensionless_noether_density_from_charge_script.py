import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge import (
    build_payload,
)


def _charge_payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_baryon_fit_used": False,
        "normalizations": {
            "projected_baryon_number_charge_Z2Sigma": 4.0,
        },
        "normalization_provenance": {
            "projected_baryon_number_charge_Z2Sigma": "active_projected_Noether_charge",
        },
    }


class DimensionlessNoetherDensityFromChargeScriptTest(unittest.TestCase):
    def test_missing_charge_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                charge_path=root / "missing.json",
                output_path=root / "density.json",
            )

            self.assertFalse(payload["gate_passed"])
            self.assertFalse((root / "density.json").exists())

    def test_valid_charge_writes_dimensionless_density(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            charge = root / "charge.json"
            output = root / "density.json"
            charge.write_text(json.dumps(_charge_payload()), encoding="utf-8")

            payload = build_payload(charge_path=charge, output_path=output)

            self.assertTrue(payload["gate_passed"])
            written = json.loads(output.read_text(encoding="utf-8"))
            self.assertAlmostEqual(
                written["dimensionless_density"][
                    "baryon_number_density0_times_Rcurv3_Z2Sigma"
                ],
                4.0 / math.pi**2,
            )
            self.assertEqual(written["remaining_dimensional_blocker"], "R_curv_Z2Sigma_m")


if __name__ == "__main__":
    unittest.main()
