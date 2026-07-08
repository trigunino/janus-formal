import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_normalization_contract_gate import (
    build_payload,
)


class Janus2024NormalizationContractGateTests(unittest.TestCase):
    def test_contract_schema_is_present(self):
        payload = build_payload()
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-normalization-contract-gate",
        )
        self.assertTrue(payload["contract_schema_present"])
        self.assertTrue(payload["cited_calibration_route_ready"])
        self.assertTrue(payload["absolute_normalization_contract_instantiated"])
        self.assertTrue(payload["reference_object_buildable_from_contract"])
        self.assertFalse(payload["paper_grade_inputs_missing"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
