import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_s2_flux_topology_gate import (
    build_payload,
)


class LLBraneS2FluxTopologyGateTests(unittest.TestCase):
    def test_s2_topology_supports_integer_flux_but_not_chi(self):
        payload = build_payload()

        self.assertTrue(payload["topology_gate_passed"])
        self.assertFalse(payload["chi_selection_gate_passed"])
        self.assertEqual(payload["topology"]["H2_S2_Z"], "Z")
        self.assertTrue(payload["closure"]["n_can_label_superselection_sector"])
        self.assertFalse(payload["closure"]["q_LL_normalization_derived"])


if __name__ == "__main__":
    unittest.main()
