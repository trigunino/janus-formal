import unittest

from scripts.build_p0_eft_janus_pt_boundary_chi_stationarity_gate import build_payload


class JanusPTBoundaryChiStationarityTests(unittest.TestCase):
    def test_pt_alone_does_not_select_nonzero_magnitude(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["pt_symmetry_result"]["PT_alone_selects_nonzero_magnitude"])
        self.assertTrue(payload["pt_symmetry_result"]["chi_zero_rejected_if_bridge_source_required"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])

    def test_next_route_is_flux_or_charge(self):
        payload = build_payload()
        required = " ".join(payload["minimal_nonzero_chi_requires_one_of"])

        self.assertIn("boundary charge", required)
        self.assertIn("flux unit", required)
        self.assertEqual(payload["best_next_after_this"], "LL_auxiliary_flux_quantizes_chi")


if __name__ == "__main__":
    unittest.main()
