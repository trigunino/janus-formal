import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate import (
    build_payload,
    write_reports,
)
from scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate import (
    build_payload as bridge_payload,
)


def bridge_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "flux_integer_n": -5,
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
        "provenance": "active_unit_flux_irreducibility",
    }


def irreducible_inputs() -> dict:
    data = bridge_inputs()
    data.update(
        {
            "Janus_PT_primitive_flux_sector_law_derived": True,
            "unit_flux_sector_only": True,
            "charge_lattice_generator_normalized": True,
            "no_multi_charge_punctures": True,
            "no_empty_spin_punctures": True,
            "minimal_nonzero_spin_representation_selected": True,
            "unit_flux_puncture_irreducible": True,
        }
    )
    return data


class SigmaUnitFluxIrreducibilityGateTests(unittest.TestCase):
    def test_missing_inputs_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["bridge_ready"])
        self.assertFalse(payload["unit_flux_irreducibility_ready"])
        self.assertFalse(payload["standard_bibliography_proves_N_gap_equals_abs_n"])

    def test_bridge_only_does_not_prove_unit_irreducibility(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(bridge_inputs()), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["bridge_ready"])
        self.assertFalse(payload["unit_flux_irreducibility_ready"])
        self.assertEqual(payload["classification"], "bridge_only_irreducibility_missing")
        self.assertIn(
            "Janus_PT_primitive_flux_sector_law_derived",
            payload["irreducibility_blocked_by"],
        )

    def test_full_irreducibility_sets_n_gap_abs_flux(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(irreducible_inputs()), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["unit_flux_irreducibility_ready"])
        self.assertTrue(payload["N_gap_equals_abs_n_ready"])
        self.assertEqual(payload["N_gap"], 5)
        self.assertEqual(payload["classification"], "derived")

    def test_observational_provenance_rejected(self):
        data = irreducible_inputs()
        data["provenance"] = "bao_fit"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["bridge_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])

    def test_write_reports_outputs_bridge_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "active"
            inp = base / "unit_flux_irreducibility_inputs.json"
            bridge = base / "chern_su2_puncture_bridge_inputs.json"
            report = Path(tmp) / "report.md"
            out = Path(tmp) / "payload.json"
            inp.parent.mkdir(parents=True)
            inp.write_text(json.dumps(irreducible_inputs()), encoding="utf-8")
            with patch(
                "scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.INPUT_PATH",
                inp,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.BRIDGE_INPUT_PATH",
                bridge,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.REPORT_PATH",
                report,
            ), patch(
                "scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.JSON_PATH",
                out,
            ):
                payload = write_reports()
                self.assertTrue(payload["bridge_ready"])
                self.assertTrue(bridge.exists())
                downstream = bridge_payload(bridge)

        self.assertTrue(downstream["N_gap_equals_abs_n_ready"])


if __name__ == "__main__":
    unittest.main()
