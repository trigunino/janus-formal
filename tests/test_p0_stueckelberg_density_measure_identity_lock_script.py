from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_density_measure_identity_lock import build_payload


class P0DensityMeasureIdentityLockTests(unittest.TestCase):
    def test_lock_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "density-measure-identity-lock-open")
        self.assertFalse(payload["density_measure_convention_fixed"])
        self.assertTrue(payload["qdet_qcross_separate"])
        self.assertFalse(payload["effective_density_continuity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_conventions_cover_phi_b_qdet_and_qcross(self) -> None:
        items = {row["item"] for row in build_payload()["convention_rows"]}

        self.assertIn("phi_jacobian_density", items)
        self.assertIn("b_measure", items)
        self.assertIn("qdet_source_measure", items)
        self.assertIn("qcross_separation", items)

    def test_blocked_identities_cover_jacobian_dlogb_continuity(self) -> None:
        identities = " ".join(build_payload()["blocked_identities"])

        self.assertIn("sqrt|g_plus| J_phi", identities)
        self.assertIn("D log B", identities)
        self.assertIn("D_receiver(B rho_to u_to)=0", identities)


if __name__ == "__main__":
    unittest.main()
