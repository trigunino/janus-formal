import unittest

from scripts.build_p0_eft_janus_z4_hard_global_theorem_availability_gate import build_payload


class P0EFTJanusZ4HardGlobalTheoremAvailabilityGateTests(unittest.TestCase):
    def test_no_hard_global_theorem_is_currently_importable_and_closed(self):
        payload = build_payload()

        self.assertFalse(payload["all_hard_global_theorems_importable_or_closed"])
        for row in payload["theorems"].values():
            self.assertFalse(row["lean_mathlib_import_available"])
            self.assertFalse(row["project_specific_geometry_match_proved"])
            self.assertFalse(row["can_close_now"])
        self.assertFalse(payload["pure_math_model_closed_without_axioms"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertEqual(
            payload["external_target_registry"],
            "p0_eft_janus_z4_hard_external_theorem_target_registry",
        )


if __name__ == "__main__":
    unittest.main()
