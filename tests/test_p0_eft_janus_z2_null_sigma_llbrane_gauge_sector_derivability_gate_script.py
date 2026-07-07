import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_gauge_sector_derivability_gate import (
    build_payload,
)


class LLBraneGaugeSectorDerivabilityGateTests(unittest.TestCase):
    def test_generic_llbrane_algebra_advances_but_does_not_select_chi(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["derived_now"]["chi_LL_is_modified_measure_composite"])
        self.assertTrue(payload["derived_now"]["spherical_S2_flux_ansatz_is_consistent"])
        self.assertFalse(
            payload["missing_for_no_rustine_chi_selection"][
                "worldvolume_charge_quantum_q_LL_derived"
            ]
        )
        self.assertFalse(
            payload["missing_for_no_rustine_chi_selection"][
                "on_shell_F2_0_derived_from_L_of_F2"
            ]
        )

    def test_four_physical_blocks_are_explicit(self):
        blocks = build_payload()["four_physical_blocks"]

        self.assertEqual(blocks["n_on_S2_throat"]["status"], "target_only")
        self.assertEqual(blocks["q_LL"]["status"], "not_derived")
        self.assertEqual(blocks["F2_0"]["status"], "not_derived")
        self.assertEqual(blocks["area_gauge"]["status"], "not_derived")


if __name__ == "__main__":
    unittest.main()
