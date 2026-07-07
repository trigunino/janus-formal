import json
import tempfile
import unittest
from pathlib import Path

from scripts import build_p0_eft_janus_z2_sigma_route_b_max_closure_gate as route_b


def write(path: Path, data: dict) -> Path:
    path.write_text(json.dumps(data), encoding="utf-8")
    return path


class SigmaRouteBMaxClosureGateTests(unittest.TestCase):
    def test_default_blocks(self):
        payload = route_b.build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["route_b_unique_prediction_ready"])
        self.assertIn("immirzi:origin_route_declared", payload["blocked_by"])

    def test_components_can_close_unique_prediction(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            im_path = write(
                base / "immirzi.json",
                {
                    "origin_route": "eta_H_trace_identity",
                    "eta_H_equals_minus_two_derived": True,
                    "gamma_abs_equals_abs_eta_H_derived": True,
                    "holst_immirzi_abs": 2.0,
                    "provenance": "active_eta_h_trace",
                },
            )
            rep_path = write(
                base / "rep.json",
                {
                    "origin_route": "minimal_nontrivial_SU2",
                    "Sigma_area_carried_by_SU2_flux": True,
                    "trivial_j0_excluded_by_nonzero_throat_area": True,
                    "provenance": "active_su2_flux",
                },
            )
            occ_path = write(
                base / "occ.json",
                {
                    "origin_route": "minimal_throat_state",
                    "ground_state_nonzero_area_required": True,
                    "provenance": "active_minimal_throat_state",
                },
            )
            payload = route_b.build_payload(
                immirzi_input=im_path,
                representation_input=rep_path,
                occupation_input=occ_path,
                area_spectrum_input=base / "spectrum.json",
                write_output=True,
            )

        self.assertTrue(payload["route_b_unique_prediction_ready"])
        self.assertFalse(payload["route_b_discrete_family_ready"])
        self.assertEqual(payload["N_gap"], 1)
        self.assertIsNotNone(payload["R_s_m"])

    def test_superselection_occupation_closes_family_not_unique_prediction(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            im_path = write(
                base / "immirzi.json",
                {
                    "origin_route": "eta_H_trace_identity",
                    "eta_H_equals_minus_two_derived": True,
                    "gamma_abs_equals_abs_eta_H_derived": True,
                    "holst_immirzi_abs": 2.0,
                    "provenance": "active_eta_h_trace",
                },
            )
            rep_path = write(
                base / "rep.json",
                {
                    "origin_route": "minimal_nontrivial_SU2",
                    "Sigma_area_carried_by_SU2_flux": True,
                    "trivial_j0_excluded_by_nonzero_throat_area": True,
                    "provenance": "active_su2_flux",
                },
            )
            occ_path = write(
                base / "occ.json",
                {
                    "origin_route": "superselection_state",
                    "N_gap": 7,
                    "N_gap_declared_as_state_sector": True,
                    "provenance": "active_area_state_sector",
                },
            )
            payload = route_b.build_payload(
                immirzi_input=im_path,
                representation_input=rep_path,
                occupation_input=occ_path,
                area_spectrum_input=base / "spectrum.json",
                write_output=True,
            )

        self.assertFalse(payload["route_b_unique_prediction_ready"])
        self.assertTrue(payload["route_b_discrete_family_ready"])
        self.assertEqual(payload["N_gap"], 7)


if __name__ == "__main__":
    unittest.main()
