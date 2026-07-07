import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate import (
    build_payload,
)


class NullSigmaLLBraneTensionToRsGateTests(unittest.TestCase):
    def test_missing_llbrane_tension_blocks_rs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["bulk_Rs_solution_available"])
        self.assertIn(
            "derive_chi_LL_abs_inverse_m_from_Janus_null_brane_action",
            payload["next_required"],
        )

    def test_active_llbrane_tension_writes_rs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "llbrane.json"
            output_path = root / "rs.json"
            input_path.write_text(
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
                        "chi_LL_abs_inverse_m": 2.0,
                        "chi_LL_provenance": "active_LL_brane_worldvolume_solution",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                input_path=input_path,
                output_path=output_path,
                write_output=True,
            )
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(
            payload["rs_payload"]["R_s_m"], 1.0 / (16.0 * math.pi)
        )
        self.assertTrue(output_exists)

    def test_fit_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "llbrane.json"
            input_path.write_text(
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
                        "chi_LL_abs_inverse_m": 2.0,
                        "chi_LL_provenance": "fit_tension",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "chi_LL_provenance_missing_or_forbidden", payload["validation_errors"]
        )


if __name__ == "__main__":
    unittest.main()
