import unittest

from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_perfect_fluid_tangency_gate import (
    build_payload,
)


class RSigmaMatterFluxRadialTermFromPerfectFluidTangencyGateTests(unittest.TestCase):
    def test_writes_zero_matter_flux_without_claiming_full_transparency(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["perfect_fluid_tangential_flux_zero_ready"])
        self.assertTrue(payload["E_matterFlux_zero_from_perfect_fluid_tangency_written"])
        self.assertFalse(payload["active_sigma_transparency_claimed"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
