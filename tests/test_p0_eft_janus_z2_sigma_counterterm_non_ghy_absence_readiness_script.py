import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_non_ghy_absence_readiness import (
    build_payload,
)


class CountertermNonGHYAbsenceReadinessTests(unittest.TestCase):
    def test_absence_is_blocked_by_incomplete_active_first_action(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["known_partition_clean"])
        self.assertFalse(payload["no_open_non_GHY_channels"])
        self.assertFalse(payload["active_first_action_assembled"])
        self.assertFalse(payload["can_prove_remaining_non_GHY_absence"])
        self.assertFalse(payload["can_promote_E_counterterm_zero"])
        self.assertIn("cross_action_source_accepted", payload["action_blockers"])
        self.assertTrue(
            payload["upstream"]["remaining_non_GHY"]["open_non_GHY_channels"][
                "metric_non_GHY_trace_R_h"
            ]
        )
        self.assertIn("do_not_prove_absence_from_incomplete_action", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
