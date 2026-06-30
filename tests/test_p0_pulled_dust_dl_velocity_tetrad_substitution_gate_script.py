from __future__ import annotations

import unittest

from scripts.build_p0_pulled_dust_dl_velocity_tetrad_substitution_gate import build_payload


class P0PulledDustDLVelocityTetradSubstitutionGateTests(unittest.TestCase):
    def test_gate_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dl-velocity-tetrad-substitution-open")
        self.assertTrue(payload["dl_velocity_tetrad_interface_written"])
        self.assertFalse(payload["all_dl_rows_closed"])
        self.assertFalse(payload["connection_force_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_el_lorentz_same_l_and_geodesic(self) -> None:
        rows = " ".join(row["gate"] for row in build_payload()["substitution_rows"])

        self.assertIn("E_L", rows)
        self.assertIn("Lorentz constraint", rows)
        self.assertIn("same L", rows)
        self.assertIn("transported geodesic", rows)

    def test_outside_scope_keeps_cuu_dphi_and_pressure_open(self) -> None:
        outside = " ".join(build_payload()["outside_scope"])

        self.assertIn("C_self-other u u", outside)
        self.assertIn("D_phi", outside)
        self.assertIn("pressure/Pi", outside)


if __name__ == "__main__":
    unittest.main()
