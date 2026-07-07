import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_sector_law_investigation import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate import (
    build_payload as irreducibility,
)


def bridge_ready_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "flux_integer_n": 6,
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
        "provenance": "active_primitive_flux_sector_law",
    }


def primitive_ready_input() -> dict:
    data = bridge_ready_input()
    data.update(
        {
            "Janus_PT_boundary_state_selects_primitive_charge": True,
            "charge_lattice_generator_normalized": True,
            "fusion_of_unit_fluxes_forbidden_by_superselection": True,
            "splitting_of_unit_flux_forbidden_by_integrality": True,
            "empty_spin_punctures_forbidden_by_area_operator_kernel": True,
            "minimal_nonzero_spin_representation_selected": True,
        }
    )
    return data


class PrimitiveFluxSectorLawInvestigationTests(unittest.TestCase):
    def test_missing_inputs_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["prerequisites_ready"])
        self.assertFalse(payload["primitive_flux_sector_law_ready"])

    def test_bridge_ready_but_law_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(bridge_ready_input()), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["prerequisites_ready"])
        self.assertFalse(payload["primitive_flux_sector_law_ready"])
        self.assertEqual(payload["classification"], "bridge_ready_law_missing")
        self.assertIn(
            "Janus_PT_boundary_state_selects_primitive_charge",
            payload["primitive_law_blocked_by"],
        )

    def test_primitive_law_writes_irreducibility_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            inp = Path(tmp) / "inputs.json"
            out = Path(tmp) / "irreducibility.json"
            inp.write_text(json.dumps(primitive_ready_input()), encoding="utf-8")
            payload = build_payload(inp, out, write_output=True)
            self.assertTrue(out.exists())
            downstream = irreducibility(out)

        self.assertTrue(payload["primitive_flux_sector_law_ready"])
        self.assertTrue(downstream["unit_flux_irreducibility_ready"])
        self.assertEqual(downstream["N_gap"], 6)

    def test_observational_provenance_rejected(self):
        data = primitive_ready_input()
        data["provenance"] = "planck_fit"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["prerequisites_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
