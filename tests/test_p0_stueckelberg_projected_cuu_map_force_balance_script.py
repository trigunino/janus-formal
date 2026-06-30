from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_projected_cuu_map_force_balance import build_payload


class P0ProjectedCuuMapForceBalanceTests(unittest.TestCase):
    def test_projected_identity_is_target_not_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "projected-force-balance-open")
        self.assertTrue(payload["projected_identity_written"])
        self.assertFalse(payload["derived_from_action"])
        self.assertFalse(payload["dust_connection_force_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_projected_identities_include_rho_h_cuu(self) -> None:
        text = " ".join(row["identity"] for row in build_payload()["projected_identities"])

        self.assertIn("rho_minus h_plus C_plus-minus", text)
        self.assertIn("u_-to+", text)
        self.assertIn("rho_plus h_minus C_minus-plus", text)
        self.assertIn("u_+to-", text)

    def test_required_checks_keep_action_mirror_integrability_open(self) -> None:
        checks = " ".join(build_payload()["required_checks"])

        self.assertIn("E_phi/E_L", checks)
        self.assertIn("mirror consistency", checks)
        self.assertIn("integrability", checks)
        self.assertIn("pressure/Pi", checks)
        self.assertIn("independent axiom", checks)


if __name__ == "__main__":
    unittest.main()
