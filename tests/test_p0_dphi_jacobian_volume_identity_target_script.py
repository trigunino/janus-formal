from __future__ import annotations

import unittest

from scripts.build_p0_dphi_jacobian_volume_identity_target import build_payload


class P0DphiJacobianVolumeIdentityTargetTests(unittest.TestCase):
    def test_identity_target_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "jacobian-volume-identity-target-open")
        self.assertTrue(payload["dphi_measure_identity_written"])
        self.assertFalse(payload["all_identities_closed"])
        self.assertFalse(payload["effective_density_continuity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_identities_cover_volume_lie_dlogb_and_continuity(self) -> None:
        identities = " ".join(row["identity"] for row in build_payload()["identities"])

        self.assertIn("sqrt|g_plus| J_phi", identities)
        self.assertIn("L_u(J_phi phi^*rho)", identities)
        self.assertIn("D log B", identities)
        self.assertIn("D_receiver(B rho_to u_to)=0", identities)

    def test_rejection_rules_forbid_measure_shortcuts(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("J_phi=1", rules)
        self.assertIn("dust 3-volume", rules)
        self.assertIn("Q_det twice", rules)
        self.assertIn("Q_cross", rules)


if __name__ == "__main__":
    unittest.main()
