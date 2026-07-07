import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_area_immirzi_source_gate import (
    build_payload as immirzi,
)
from scripts.build_p0_eft_janus_z2_sigma_area_occupation_selection_gate import (
    build_payload as occupation,
)
from scripts.build_p0_eft_janus_z2_sigma_area_representation_selector_gate import (
    build_payload as representation,
)


class SigmaAreaSubselectorTests(unittest.TestCase):
    def test_immirzi_eta_trace_route(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "immirzi.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "eta_H_trace_identity",
                        "eta_H_equals_minus_two_derived": True,
                        "gamma_abs_equals_abs_eta_H_derived": True,
                        "holst_immirzi_abs": 2.0,
                        "provenance": "active_eta_h_trace",
                    }
                ),
                encoding="utf-8",
            )
            payload = immirzi(path)

        self.assertTrue(payload["immirzi_source_ready"])
        self.assertEqual(payload["holst_immirzi_abs"], 2.0)

    def test_representation_minimal_su2_route_sets_half(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "rep.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "minimal_nontrivial_SU2",
                        "Sigma_area_carried_by_SU2_flux": True,
                        "trivial_j0_excluded_by_nonzero_throat_area": True,
                        "provenance": "active_su2_flux",
                    }
                ),
                encoding="utf-8",
            )
            payload = representation(path)

        self.assertTrue(payload["representation_selector_ready"])
        self.assertEqual(payload["j_min"], 0.5)

    def test_occupation_flux_area_lock_uses_abs_flux_integer(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "occ.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "flux_area_lock",
                        "flux_integer_n": -4,
                        "one_area_puncture_per_flux_unit_derived": True,
                        "provenance": "active_flux_area_lock",
                    }
                ),
                encoding="utf-8",
            )
            payload = occupation(path)

        self.assertTrue(payload["occupation_selector_ready"])
        self.assertTrue(payload["N_gap_is_unique_prediction"])
        self.assertEqual(payload["N_gap"], 4)

    def test_occupation_superselection_is_not_unique_prediction(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "occ.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "superselection_state",
                        "N_gap": 9,
                        "N_gap_declared_as_state_sector": True,
                        "provenance": "active_area_state_sector",
                    }
                ),
                encoding="utf-8",
            )
            payload = occupation(path)

        self.assertTrue(payload["occupation_selector_ready"])
        self.assertFalse(payload["N_gap_is_unique_prediction"])
        self.assertTrue(payload["N_gap_is_superselection_label"])


if __name__ == "__main__":
    unittest.main()
