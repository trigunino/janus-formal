import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate import (
    build_payload,
    write_reports,
)
from scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate import (
    build_payload as puncture_theorem,
)


def valid_bridge_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "flux_integer_n": 4,
        "S2_throat_cycle_defined": True,
        "global_U1_bundle_on_S2_throat": True,
        "c1_flux_equals_n": True,
        "Holst_Ashtekar_Barbero_variables_on_Sigma": True,
        "SU2_spin_bundle_on_Sigma_derived": True,
        "Sigma_boundary_type": "null_PT_throat",
        "horizon_Chern_Simons_boundary_condition_projected": True,
        "spin_network_edges_can_end_on_Sigma": True,
        "transverse_intersection_number_defined": True,
        "Gauss_constraint_links_CS_defects_to_spin_flux": True,
        "area_gauge": "physical_induced_S2_metric",
        "provenance": "active_sigma_chern_su2_bridge",
    }


class SigmaChernSU2PunctureBridgeGateTests(unittest.TestCase):
    def test_missing_inputs_blocks_bridge(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["chern_to_su2_puncture_bridge_ready"])
        self.assertIn("SU2_spin_bundle_on_Sigma_derived", payload["blocked_by"])

    def test_bridge_ready_does_not_imply_n_gap_equals_abs_n(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(valid_bridge_inputs()), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["chern_to_su2_puncture_bridge_ready"])
        self.assertFalse(payload["N_gap_equals_abs_n_ready"])
        self.assertIn("unit_flux_sector_only", payload["irreducibility_blocked_by"])
        self.assertFalse(payload["theorem_payload"]["one_puncture_per_unit_flux_derived"])

    def test_full_unit_flux_irreducibility_writes_theorem_ready_payload(self):
        data = valid_bridge_inputs()
        data.update(
            {
                "unit_flux_sector_only": True,
                "no_multi_charge_punctures": True,
                "no_empty_spin_punctures": True,
                "unit_flux_puncture_irreducible": True,
            }
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)
            theorem_path = Path(tmp) / "theorem.json"
            theorem_path.write_text(json.dumps(payload["theorem_payload"]), encoding="utf-8")
            theorem = puncture_theorem(theorem_path)

        self.assertTrue(payload["N_gap_equals_abs_n_ready"])
        self.assertTrue(theorem["puncture_theorem_ready"])
        self.assertEqual(theorem["N_gap"], 4)

    def test_observational_provenance_rejected(self):
        data = valid_bridge_inputs()
        data["provenance"] = "planck_fit"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["chern_to_su2_puncture_bridge_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])

    def test_write_reports_outputs_theorem_payload_when_bridge_ready(self):
        data = valid_bridge_inputs()
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "active"
            inp = base / "chern_su2_puncture_bridge_inputs.json"
            theorem = base / "flux_area_puncture_theorem_inputs.json"
            report = Path(tmp) / "report.md"
            out = Path(tmp) / "payload.json"
            inp.parent.mkdir(parents=True)
            inp.write_text(json.dumps(data), encoding="utf-8")
            with patch(
                "scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate.INPUT_PATH",
                inp,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate.THEOREM_INPUT_PATH",
                theorem,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate.REPORT_PATH",
                report,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate.JSON_PATH",
                out,
            ):
                payload = write_reports()
                self.assertTrue(payload["chern_to_su2_puncture_bridge_ready"])
                self.assertTrue(theorem.exists())


if __name__ == "__main__":
    unittest.main()
