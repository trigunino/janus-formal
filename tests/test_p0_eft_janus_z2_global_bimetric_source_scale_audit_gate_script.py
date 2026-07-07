import unittest

from scripts.build_p0_eft_janus_z2_global_bimetric_source_scale_audit_gate import (
    build_payload,
)


class GlobalBimetricSourceScaleAuditGateTests(unittest.TestCase):
    def test_audit_keeps_global_equations_but_blocks_absolute_scale(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["global_bimetric_equations_available"])
        self.assertTrue(payload["Souriau_PT_sign_pairing_available"])
        self.assertTrue(payload["published_relative_sector_ratio_available"])
        self.assertAlmostEqual(payload["rho_minus0_over_rho_plus0"], -19.0)
        self.assertFalse(payload["absolute_mass_scale_found"])
        self.assertTrue(payload["topology_only_scale_free"])
        self.assertIn(
            "global_Noether_or_Hamiltonian_mass_charge",
            payload["missing_inputs"],
        )


if __name__ == "__main__":
    unittest.main()
