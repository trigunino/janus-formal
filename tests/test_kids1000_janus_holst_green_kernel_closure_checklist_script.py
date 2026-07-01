from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_green_kernel_closure_checklist import build_payload, checklist_rows


class KiDS1000JanusHolstGreenKernelClosureChecklistTests(unittest.TestCase):
    def test_payload_blocks_value_slip_until_green_kernel_is_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "green-kernel-closure-checklist-open")
        self.assertFalse(payload["green_kernel_computed"])
        self.assertFalse(payload["can_enable_value_slip"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["found_derivation_status"]["complete_value_derivation_found"])
        self.assertEqual(
            payload["found_derivation_status"]["projected_green_calculation"],
            "regulated-spectral-green-scheme-dependent",
        )
        self.assertGreater(len(payload["blockers"]), 0)

    def test_checklist_rows_are_machine_readable(self) -> None:
        scaffold = {"uses_kids_residuals": False, "uses_delta_z": False, "uses_bin_factors": False, "green_kernel_computed": False}
        neumann = {"theorem_status": {"target_kernel_identified": True, "green_kernel_computed": False}}
        dust_green = {
            "boundary_conditions_source_derived": False,
            "zero_mode_policy_written": True,
            "qdet_convention_selected_from_source": False,
            "same_l_qcross_selected": False,
        }

        ds3 = {"theorem_status": {"green_kernel_equals_three_halves_H_proved": False}}

        projected_green = {"scheme_dependent": True}

        rows = checklist_rows(scaffold, neumann, dust_green, ds3, projected_green)

        self.assertTrue(all({"check", "passed", "blocker"} <= set(row) for row in rows))
        self.assertTrue(any(row["check"] == "finite_mode_green_kernel_computed" for row in rows))
        self.assertTrue(any(row["check"] == "ds3_renormalized_response_proved" for row in rows))
        self.assertTrue(any(row["check"] == "projected_green_scheme_fixed" for row in rows))


if __name__ == "__main__":
    unittest.main()
