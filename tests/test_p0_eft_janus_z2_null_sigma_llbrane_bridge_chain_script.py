import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.run_p0_eft_janus_z2_null_sigma_llbrane_bridge_chain import build_payload


class NullSigmaLLBraneBridgeChainTests(unittest.TestCase):
    def test_missing_llbrane_input_blocks_at_first_stage(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                llbrane_input=root / "missing.json",
                bulk_rs_path=root / "bulk_rs.json",
                global_mass_path=root / "global_mass.json",
                mass_charge_path=root / "mass_charge.json",
                rs_scale_path=root / "rs_scale.json",
                write_output=True,
            )

        self.assertFalse(payload["chain_passed"])
        self.assertEqual(payload["first_blocker"], "llbrane_tension_to_Rs")

    def test_valid_llbrane_input_materializes_full_chain(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            llbrane_input = root / "llbrane.json"
            llbrane_input.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived_llbrane",
                        "extension_status": "explicit_LL_brane_source",
                        "llbrane_action_accepted": True,
                        "horizon_straddling_proved": True,
                        "a0": 0.125,
                        "chi_LL_sign": "negative",
                        "chi_LL_abs_inverse_m": 1.0,
                        "chi_LL_provenance": "active_LL_brane_worldvolume_solution",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            rs_scale_path = root / "rs_scale.json"
            payload = build_payload(
                llbrane_input=llbrane_input,
                bulk_rs_path=root / "bulk_rs.json",
                global_mass_path=root / "global_mass.json",
                mass_charge_path=root / "mass_charge.json",
                rs_scale_path=rs_scale_path,
                write_output=True,
            )
            output_exists = rs_scale_path.exists()

        self.assertTrue(payload["chain_passed"])
        self.assertAlmostEqual(
            payload["final_rs_scale_payload"]["R_s_m"], 1.0 / (8.0 * math.pi)
        )
        self.assertTrue(output_exists)


if __name__ == "__main__":
    unittest.main()
