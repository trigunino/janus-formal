import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    C_SI,
    G_SI,
    build_payload,
)


def superselection_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "area_operator_on_Sigma_derived": True,
        "Holst_area_spectrum_law_derived": True,
        "area_gauge": "physical_induced_S2_metric",
        "superselection_sector_law_declared": True,
        "N_gap_sectors": [1, 2],
        "holst_immirzi_abs": 2.0,
        "j_min": 0.5,
        "provenance": "active_sigma_area_superselection",
    }


class SigmaDiscreteFamilyPropagationTests(unittest.TestCase):
    def test_missing_inputs_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json", Path(tmp) / "missing_super.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["discrete_family_propagation_ready"])
        self.assertIn("area_superselection_family_ready", payload["blocked_by"])

    def test_propagates_superselection_family_without_selecting_sector(self):
        with tempfile.TemporaryDirectory() as tmp:
            super_path = Path(tmp) / "super.json"
            input_path = Path(tmp) / "inputs.json"
            super_path.write_text(json.dumps(superselection_input()), encoding="utf-8")
            input_path.write_text(
                json.dumps(
                    {
                        "superselection_input_path": str(super_path),
                        "flux_integer_n": 3,
                        "provenance": "active_discrete_family",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path)

        self.assertTrue(payload["discrete_family_propagation_ready"])
        self.assertFalse(payload["unique_prediction_ready"])
        self.assertEqual([item["N_gap"] for item in payload["sector_table"]], [1, 2])
        first = payload["sector_table"][0]
        self.assertAlmostEqual(first["M_bridge_kg"], C_SI**2 * first["R_s_m"] / (2.0 * G_SI))
        self.assertAlmostEqual(
            first["lambda_F2_over_q_LL_m_minus_2"],
            first["R_s_m"] ** 2 / (math.sqrt(8.0) * 3.0),
        )

    def test_observational_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            super_path = Path(tmp) / "super.json"
            input_path = Path(tmp) / "inputs.json"
            super_path.write_text(json.dumps(superselection_input()), encoding="utf-8")
            input_path.write_text(
                json.dumps({"superselection_input_path": str(super_path), "provenance": "planck_fit"}),
                encoding="utf-8",
            )
            payload = build_payload(input_path)

        self.assertFalse(payload["discrete_family_propagation_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
