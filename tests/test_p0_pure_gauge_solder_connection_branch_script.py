from __future__ import annotations

import unittest

from scripts.build_p0_pure_gauge_solder_connection_branch import build_payload


class P0PureGaugeSolderConnectionBranchTests(unittest.TestCase):
    def test_branch_is_flat_candidate_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["construction_written"])
        self.assertTrue(payload["flat_if_global_lorentz_l"])
        self.assertFalse(payload["source_derived_lorentz_projection"])
        self.assertFalse(payload["zero_divergence_verified"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_construction_uses_solder_polar_and_omega(self) -> None:
        text = " ".join(build_payload()["construction"])

        self.assertIn("L_geom=e_plus E_minus", text)
        self.assertIn("polar_eta", text)
        self.assertIn("Omega=(D L)L^{-1}", text)
        self.assertIn("R_Omega=0", text)

    def test_blockers_include_projection_holonomy_and_pde(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("not Lorentz", blockers)
        self.assertIn("polar projection", blockers)
        self.assertIn("holonomy", blockers)
        self.assertIn("zero-divergence PDE", blockers)


if __name__ == "__main__":
    unittest.main()
