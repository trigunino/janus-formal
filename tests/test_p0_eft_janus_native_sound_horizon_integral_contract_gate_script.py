import unittest

from janus_lab.janus_phase_space_occupation_search import (
    native_sound_horizon_integral_contract_payload,
)


class JanusNativeSoundHorizonIntegralContractGateTests(unittest.TestCase):
    def test_sound_horizon_exposes_drag_convergence_tension(self):
        payload = native_sound_horizon_integral_contract_payload()
        rows = {row["name"]: row for row in payload["candidate_H_scalings"]}

        self.assertTrue(rows["radiation_like"]["finite_if_integrated_from_a0"])
        self.assertFalse(rows["matter_or_curvature_boundary"]["finite_if_integrated_from_a0"])
        self.assertFalse(rows["bridge_or_vacuum_shallow"]["finite_if_integrated_from_a0"])

    def test_janus_resolution_requires_nonzero_lower_bound_or_transition(self):
        payload = native_sound_horizon_integral_contract_payload()

        self.assertIn("a_min>0", payload["janus_resolution"])
        self.assertTrue(
            any("derive active a_min/throat lower bound" in item for item in payload["remaining"])
        )


if __name__ == "__main__":
    unittest.main()
