from __future__ import annotations

import unittest

from scripts.build_p0_eft_chi_infinity_stationary_closure import build_payload, stationary_solution


class P0EFTChiInfinityStationaryClosureTests(unittest.TestCase):
    def test_cosh_alone_has_zero_stationary_point(self) -> None:
        solution = stationary_solution()

        self.assertIn("J_bg=0", solution["cosh_alone_solution"])
        self.assertIn("chi_inf=0", solution["cosh_alone_solution"])

    def test_nonzero_solution_needs_background_force(self) -> None:
        solution = stationary_solution()

        self.assertIn("asinh", solution["nonzero_solution"])
        self.assertEqual(solution["required_background_force"], "J_bg != 0")

    def test_status_keeps_jbg_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["nonzero_chi_inf_requires_background_source"])
        self.assertFalse(status["J_bg_derived_from_Janus_background"])
        self.assertFalse(status["amplitude_fully_closed"])

    def test_obligations_point_to_junction_source(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("J_bg", obligations)
        self.assertIn("Einstein-Palatini junction", obligations)


if __name__ == "__main__":
    unittest.main()
