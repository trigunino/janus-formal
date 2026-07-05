import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_acyclic_route_selection_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaMatterFluxAcyclicRouteSelectionGateTests(unittest.TestCase):
    def test_current_route_selects_coupled_system_and_blocks(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["transparency_depends_on_unknown_embedding"])
        self.assertFalse(payload["transparency_acyclic_ready"])
        self.assertEqual(payload["selected_nonfit_route"], "coupled_radius_flux")
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["independent_flux_shortcut_forbidden"])
        self.assertFalse(payload["uses_archived_z4"])
        self.assertIn("solve_coupled_RSigma_Flux_system_without_fit", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
