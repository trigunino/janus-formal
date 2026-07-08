import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_bao_contract_audit import (
    build_payload,
)


class Janus2024BAOContractAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_bao_boundary_is_explicit(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-bao-contract-audit",
        )
        self.assertTrue(payload["native_bao_geometry_basis_present"])
        self.assertFalse(payload["native_bao_ruler_closed"])
        self.assertFalse(payload["native_bao_observable_contract_closed"])
        self.assertTrue(payload["step4_source_boundary_reached"])


if __name__ == "__main__":
    unittest.main()
