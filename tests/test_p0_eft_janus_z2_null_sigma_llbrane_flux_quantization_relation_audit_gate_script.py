import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate import (
    build_payload,
)


class LLBraneFluxQuantizationRelationAuditGateTests(unittest.TestCase):
    def test_flux_relation_blocks_on_quantum_gauge_and_F2(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["flux_relation_closes_chi"])
        self.assertEqual(payload["topology"]["natural_flux_cycle"], "S2_throat")
        self.assertIn(
            "worldvolume_charge_normalization_derived", payload["blocked_by"]
        )
        self.assertIn(
            "auxiliary_metric_to_physical_area_gauge_fixed", payload["blocked_by"]
        )
        self.assertIn("F2_constant_from_Janus_action_derived", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
