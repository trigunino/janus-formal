import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate import (
    build_payload,
    write_reports,
)


def valid_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "flux_integer_n": -3,
        "S2_throat_cycle_defined": True,
        "global_U1_bundle_on_S2_throat": True,
        "c1_flux_equals_n": True,
        "U1_to_SU2_puncture_map_derived": True,
        "local_puncture_index_theorem_derived": True,
        "puncture_area_operator_coupled_to_flux_derived": True,
        "one_puncture_per_unit_flux_derived": True,
        "no_puncture_without_flux_derived": True,
        "unit_flux_puncture_irreducible": True,
        "area_gauge": "physical_induced_S2_metric",
        "provenance": "active_sigma_flux_area_puncture_theorem",
    }


class SigmaFluxAreaPunctureTheoremGateTests(unittest.TestCase):
    def test_missing_inputs_blocks_without_failing_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["puncture_theorem_ready"])
        self.assertIn("flux_integer_n_available", payload["blocked_by"])
        self.assertIn("U1_to_SU2_puncture_map_derived", payload["blocked_by"])

    def test_valid_puncture_theorem_sets_n_gap_abs_flux(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(valid_inputs()), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["puncture_theorem_ready"])
        self.assertEqual(payload["N_gap"], 3)
        self.assertEqual(payload["occupation_payload"]["origin_route"], "flux_area_lock")
        self.assertEqual(payload["occupation_payload"]["flux_integer_n"], -3)

    def test_topological_flux_without_puncture_map_is_not_enough(self):
        data = valid_inputs()
        data["U1_to_SU2_puncture_map_derived"] = False
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["puncture_theorem_ready"])
        self.assertIn("U1_to_SU2_puncture_map_derived", payload["blocked_by"])
        self.assertIsNone(payload["N_gap"])

    def test_observational_provenance_rejected(self):
        data = valid_inputs()
        data["provenance"] = "fit_planck"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["puncture_theorem_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])

    def test_write_reports_emits_occupation_payload_when_ready(self):
        data = valid_inputs()
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "active"
            report = Path(tmp) / "report.md"
            out = Path(tmp) / "payload.json"
            occ = base / "sigma_area_occupation_selection_inputs.json"
            inp = base / "flux_area_puncture_theorem_inputs.json"
            inp.parent.mkdir(parents=True)
            inp.write_text(json.dumps(data), encoding="utf-8")
            with patch(
                "scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.INPUT_PATH",
                inp,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.REPORT_PATH",
                report,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.JSON_PATH",
                out,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.OCCUPATION_OUTPUT_PATH",
                occ,
            ):
                payload = write_reports()

            self.assertTrue(payload["puncture_theorem_ready"])
            self.assertTrue(occ.exists())
            written = json.loads(occ.read_text(encoding="utf-8"))
            self.assertEqual(written["origin_route"], "flux_area_lock")


if __name__ == "__main__":
    unittest.main()
