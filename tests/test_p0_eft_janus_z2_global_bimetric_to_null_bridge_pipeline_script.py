import unittest

from scripts.run_p0_eft_janus_z2_global_bimetric_to_null_bridge_pipeline import (
    build_payload,
)


class GlobalBimetricToNullBridgePipelineTests(unittest.TestCase):
    def test_pipeline_blocks_without_global_mass_state(self):
        payload = build_payload(write_intermediate=False)

        self.assertFalse(payload["pipeline_passed"])
        self.assertFalse(payload["global_mass_state_available"])
        self.assertFalse(payload["absolute_Rs_selected"])
        self.assertIn(
            "derive_global_bimetric_stress_energy_state_or_clean_mass_state",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
