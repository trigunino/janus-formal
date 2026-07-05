import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_primitive_integration_gate import (
    build_payload,
)


def _integrability_ready():
    return {
        "status": "injected-integrability",
        "counterterm_residual_integrability_ready": True,
        "primary_blocker": "none",
        "closure": {"residual_one_form_exact": True},
    }


class CountertermPrimitiveIntegrationGateTests(unittest.TestCase):
    def test_default_blocks_on_integrability(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["closure"]["residual_one_form_exact"])
        self.assertIn("residual_one_form_exact = false", payload["current_frontier"])

    def test_exact_residual_still_requires_primitive_data(self):
        payload = build_payload(integrability_payload=_integrability_ready())

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "counterterm_primitive_density")
        self.assertFalse(payload["closure"]["primitive_density_supplied"])

    def test_ready_primitive_passes(self):
        payload = build_payload(
            integrability_payload=_integrability_ready(),
            primitive_payload={
                "primitive_density_supplied": True,
                "primitive_cancels_residual": True,
                "primitive_unique_up_to_constant": True,
                "no_new_counterterm_freedom": True,
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["counterterm_primitive_integration_ready"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
