from __future__ import annotations

import unittest

from scripts.build_p0_dl_dlogb_identity_targets import build_payload


class P0DlDlogBIdentityTargetsTests(unittest.TestCase):
    def test_identity_targets_are_written_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["dl_identities_written"])
        self.assertTrue(payload["dlogb_identities_written"])
        self.assertFalse(payload["all_identities_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_dl_targets_require_lorentz_generator_and_mirror(self) -> None:
        text = " ".join(row["expanded"] for row in build_payload()["dl_targets"])

        self.assertIn("D_alpha L", text)
        self.assertIn("F_alpha^T eta + eta F_alpha = 0", text)
        self.assertIn("L_plus_to_minus", text)

    def test_dlogb_targets_keep_lapse_and_4volume_terms(self) -> None:
        text = " ".join(row["expanded"] for row in build_payload()["dlogb_targets"])

        self.assertIn("log(-g_minus)", text)
        self.assertIn("log(-g_plus)", text)
        self.assertIn("D log N_other/N_self", text)
        self.assertIn("3 D log a_other/a_self", text)

    def test_rejections_block_artificial_closure(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("reject D L=0", rules)
        self.assertIn("reject B_4vol=V3_dust", rules)
        self.assertIn("Q_cross", rules)
        self.assertIn("closed=false", rules)


if __name__ == "__main__":
    unittest.main()
