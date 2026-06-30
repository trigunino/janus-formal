from __future__ import annotations

import unittest

from scripts.build_p0_flat_omega_connection_branch import build_payload


class P0FlatOmegaConnectionBranchTests(unittest.TestCase):
    def test_flat_branch_is_written_but_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["flatness_condition_written"])
        self.assertTrue(payload["path_independence_if_flat"])
        self.assertFalse(payload["source_derived_flatness"])
        self.assertFalse(payload["unique_l_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_flatness_conditions_include_curvature_and_path_ordering(self) -> None:
        conditions = " ".join(build_payload()["flatness_conditions"])

        self.assertIn("D_alpha L = Omega_alpha L", conditions)
        self.assertIn("R_Omega", conditions)
        self.assertIn("[Omega_alpha,Omega_beta]", conditions)
        self.assertIn("P exp", conditions)

    def test_solves_path_but_not_omega_or_l0(self) -> None:
        solves = " ".join(build_payload()["what_it_solves"])
        not_solves = " ".join(build_payload()["what_it_does_not_solve"])

        self.assertIn("path ambiguity", solves)
        self.assertIn("Lorentz admissibility", solves)
        self.assertIn("does not determine Omega", not_solves)
        self.assertIn("does not fix L0", not_solves)

    def test_possible_routes_include_pure_gauge_holonomy_and_restriction(self) -> None:
        routes = " ".join(build_payload()["possible_source_routes"])

        self.assertIn("pure-gauge", routes)
        self.assertIn("holonomy", routes)
        self.assertIn("FLRW", routes)


if __name__ == "__main__":
    unittest.main()
