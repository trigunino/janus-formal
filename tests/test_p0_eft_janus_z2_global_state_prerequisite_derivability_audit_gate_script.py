import unittest

from scripts.build_p0_eft_janus_z2_global_state_prerequisite_derivability_audit_gate import (
    build_payload,
)


class GlobalStatePrerequisiteDerivabilityAuditGateTests(unittest.TestCase):
    def test_live_repo_blocks_charge_and_volume_derivation(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["global_matter_state_can_be_derived_now"])
        self.assertFalse(payload["projected_baryon_noether_charge"]["can_derive_now"])
        self.assertFalse(payload["active_R_curv_volume"]["can_derive_now"])
        self.assertIn("spinor", " ".join(payload["non_rustine_blockers"]))
        self.assertIn("R_Sigma", " ".join(payload["non_rustine_blockers"]))


if __name__ == "__main__":
    unittest.main()
