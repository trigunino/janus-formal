import unittest

from scripts.build_p0_eft_janus_z4_hard_external_theorem_target_registry import (
    build_payload,
)


class P0EFTJanusZ4HardExternalTheoremTargetRegistryTests(unittest.TestCase):
    def test_registry_declares_targets_without_no_fit_promotion(self):
        payload = build_payload()

        self.assertTrue(payload["registry_complete"])
        self.assertTrue(payload["imported_theorem_may_replace_only_matching_target"])
        self.assertTrue(payload["no_fit_promotion_requires_all_targets_closed"])
        self.assertFalse(payload["all_hard_targets_closed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertIn(
            "pin_minus_lift_squared_minus_one",
            payload["targets"]["aps_pin_global_index"]["accepted_import_must_prove"],
        )
        self.assertFalse(
            payload["targets"]["unique_action_to_equations"]["can_be_replaced_by_import"]
        )


if __name__ == "__main__":
    unittest.main()
