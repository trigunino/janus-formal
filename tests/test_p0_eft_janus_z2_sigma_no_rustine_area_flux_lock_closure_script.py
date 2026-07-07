import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_no_rustine_area_flux_lock_closure import (
    build_payload,
)


def base_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "area_gauge": "physical_induced_S2_metric",
        "provenance": "active_no_rustine_area_flux_lock",
        "SU2_or_spin_structure_on_Sigma_derived": True,
        "Sigma_area_carried_by_SU2_flux": True,
        "trivial_j0_excluded_by_nonzero_throat_area": True,
        "eta_H_equals_minus_two_derived": True,
        "gamma_abs_equals_abs_eta_H_derived": True,
        "trace_normalization_matches_area_spectrum": True,
    }


class NoRustineAreaFluxLockClosureTests(unittest.TestCase):
    def test_default_blocks(self):
        payload = build_payload(Path("missing-no-rustine.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["route_b_inputs_ready"])
        self.assertIn("base:active_core_Z2_tunnel_Sigma", payload["blocked_by"])

    def test_flux_area_lock_outputs_route_b_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "closure.json"
            data = base_input()
            data.update(
                {
                    "flux_integer_n": -5,
                    "global_U1_bundle_on_S2_throat": True,
                    "one_area_puncture_per_flux_unit_derived": True,
                    "no_puncture_without_flux_derived": True,
                    "unit_flux_puncture_irreducible": True,
                }
            )
            input_path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(
                input_path,
                immirzi_output=base / "immirzi.json",
                representation_output=base / "rep.json",
                occupation_output=base / "occ.json",
                write_output=True,
            )

            occ = json.loads((base / "occ.json").read_text(encoding="utf-8"))

        self.assertTrue(payload["route_b_inputs_ready"])
        self.assertEqual(payload["N_gap"], 5)
        self.assertEqual(payload["N_gap_origin"], "flux_area_lock")
        self.assertEqual(occ["origin_route"], "flux_area_lock")
        self.assertEqual(occ["flux_integer_n"], -5)

    def test_minimal_throat_fallback_outputs_route_b_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "closure.json"
            data = base_input()
            data.update(
                {
                    "ground_state_nonzero_area_required": True,
                    "N0_absent_because_no_throat": True,
                    "minimal_throat_stability_checked": True,
                }
            )
            input_path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(
                input_path,
                immirzi_output=base / "immirzi.json",
                representation_output=base / "rep.json",
                occupation_output=base / "occ.json",
                write_output=True,
            )

        self.assertTrue(payload["route_b_inputs_ready"])
        self.assertEqual(payload["N_gap"], 1)
        self.assertEqual(payload["N_gap_origin"], "minimal_throat_state")

    def test_observational_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "closure.json"
            data = base_input()
            data["provenance"] = "planck fit"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["route_b_inputs_ready"])
        self.assertIn("base:non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
