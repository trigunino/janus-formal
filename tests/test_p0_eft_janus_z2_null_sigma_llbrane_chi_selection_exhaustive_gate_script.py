import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_chi_selection_exhaustive_gate import (
    build_payload,
)


class LLBraneChiSelectionExhaustiveGateTests(unittest.TestCase):
    def test_current_nonfit_routes_do_not_select_chi(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_abs_inverse_m_ready"])
        self.assertTrue(payload["all_current_nonfit_routes_exhausted"])
        self.assertEqual(payload["closed_routes"], [])

    def test_expected_routes_are_accounted_for(self):
        payload = build_payload()
        routes = payload["route_status"]

        self.assertIn("worldvolume_local_eom", routes)
        self.assertIn("PT_boundary_state", routes)
        self.assertIn("S2_flux_quantization", routes)
        self.assertIn("global_mass_chi_matching", routes)
        self.assertIn(
            "do_not_keep_chi_LL_and_M_bridge_independent",
            payload["forbidden_shortcuts"],
        )

    def test_remaining_exits_are_non_observational(self):
        payload = build_payload()
        exits = " ".join(payload["remaining_nonfit_exits"])

        self.assertIn("q_LL", exits)
        self.assertIn("Noether mass", exits)
        self.assertIn("extension-state input", exits)


if __name__ == "__main__":
    unittest.main()
