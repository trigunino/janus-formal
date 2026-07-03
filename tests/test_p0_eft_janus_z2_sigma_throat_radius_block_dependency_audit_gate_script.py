import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_block_dependency_audit_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGateTests(unittest.TestCase):
    def test_dependency_audit_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_block_dependencies_declared"])
        self.assertTrue(payload["declared"]["matter_flux_radial_block_gate_declared"])
        self.assertTrue(payload["declared"]["counterterm_radial_block_gate_declared"])

    def test_dependency_audit_blocks_radius_solution(self):
        payload = build_payload()

        self.assertFalse(payload["reduced"]["matter_flux_block_reduced"])
        self.assertFalse(payload["reduced"]["counterterm_block_reduced"])
        self.assertFalse(payload["missing_radius_blocks_closed"])
        self.assertFalse(payload["allowed"]["E_RSigma_expansion_allowed"])
        self.assertFalse(payload["allowed"]["R_Sigma_solution_allowed"])
        self.assertIn("close_matter_flux_radial_block_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
