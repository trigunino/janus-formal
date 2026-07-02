import unittest

from scripts.build_p0_eft_janus_z4_bimetric_scalar_variables_gate import build_payload as build_variables
from scripts.build_p0_eft_janus_z4_derived_slip_regeneration_readiness_gate import build_payload as build_readiness
from scripts.build_p0_eft_janus_z4_traceless_spatial_slip_equation_gate import build_payload as build_equation


class P0EFTJanusZ4DerivedSlipScaffoldingTests(unittest.TestCase):
    def test_bimetric_scalar_variables_declared(self):
        payload = build_variables()

        self.assertTrue(payload["variables_gate_passed"])
        self.assertTrue(payload["visible_metric_potentials_declared"])
        self.assertTrue(payload["hidden_or_negative_metric_potentials_declared"])
        self.assertTrue(payload["projection_terms_declared"])
        self.assertEqual(payload["torsion_terms_status"], "explicit_zero_until_derived")
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["planck_trial_allowed"])

    def test_traceless_spatial_equation_available(self):
        payload = build_equation()

        self.assertTrue(payload["slip_equation_gate_passed"])
        self.assertTrue(payload["slip_source_derived_from_field_equations"])
        self.assertIn("Lap_TF(delta_slip_Z4)", payload["source_operator"])
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertFalse(payload["free_slip_amplitude"])
        self.assertFalse(payload["value_slip_transport_closed"])
        self.assertFalse(payload["planck_trial_allowed"])

    def test_regeneration_readiness_remains_blocked_by_value_transport(self):
        payload = build_readiness()

        self.assertFalse(payload["derived_slip_regeneration_ready"])
        self.assertTrue(payload["boundary_green_or_normal_mode_required"])
        self.assertFalse(payload["deltaSlip_Z4_regenerated_per_cosmology"])
        self.assertFalse(payload["planck_trial_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
