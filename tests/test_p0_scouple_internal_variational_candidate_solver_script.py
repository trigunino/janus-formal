from __future__ import annotations

import unittest

from scripts.build_p0_scouple_internal_variational_candidate_solver import (
    build_payload,
    render_markdown,
)


class P0ScoupleInternalVariationalCandidateSolverTests(unittest.TestCase):
    def test_internal_solver_kills_c0_c1_but_not_family(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "internal-variational-candidate-open")
        self.assertIn("c0", payload["combined_solution"])
        self.assertIn("c1", payload["combined_solution"])
        self.assertEqual(payload["remaining_free_coefficients_after_basic_closure"], ["c2", "c3"])
        self.assertTrue(payload["aligned_branch_stationary"])
        self.assertTrue(payload["zero_vacuum_energy_fixed"])
        self.assertFalse(payload["unique_phi_forced"])

    def test_l_equation_is_algebraic_not_transport(self) -> None:
        payload = build_payload()

        self.assertIn("l0", payload["e_l0"])
        self.assertIn("l1", payload["e_l1"])
        self.assertEqual(payload["e_l_after_constraints"], ["0", "0"])
        self.assertFalse(payload["el_is_transport_equation"])

    def test_acceptance_checks_keep_real_blockers_open(self) -> None:
        rows = {row["check"]: row for row in build_payload()["acceptance_checks"]}

        self.assertTrue(rows["aligned_stationarity"]["closed"])
        self.assertTrue(rows["zero_aligned_vacuum_energy"]["closed"])
        self.assertFalse(rows["unique_local_phi"]["closed"])
        self.assertFalse(rows["L_transport"]["closed"])
        self.assertFalse(rows["split_noether"]["closed"])
        self.assertFalse(rows["pressure_pi"]["closed"])

    def test_no_fit_and_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["accepted_scouple_action_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_mentions_open_pressure_pi(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Remaining free coefficients: c2, c3", markdown)
        self.assertIn("E_L is transport equation: False", markdown)
        self.assertIn("Pressure/Pi closed: False", markdown)


if __name__ == "__main__":
    unittest.main()
