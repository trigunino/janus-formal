import unittest

from scripts.build_p0_eft_janus_z2_sigma_nocc_boundary_state_selection_gate import (
    build_payload,
)


class NOccBoundaryStateSelectionGateTests(unittest.TestCase):
    def test_nocc_is_state_label_not_density(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["Q_Sigma_equals_N_occ"])
        self.assertFalse(payload["closure"]["charge_conservation_selects_unique_N_occ"])
        self.assertFalse(payload["closure"]["N_occ_numeric_ready"])
        self.assertFalse(payload["ready_for_projected_occupation_state_inputs"])
        self.assertIn("do_not_fit_N_occ_to_BAO_or_CMB", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
