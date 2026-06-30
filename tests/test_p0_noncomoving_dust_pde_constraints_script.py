from __future__ import annotations

import unittest

from scripts.build_p0_noncomoving_dust_pde_constraints import build_payload


class P0NoncomovingDustPdeConstraintsTests(unittest.TestCase):
    def test_constraints_are_written_but_not_unique(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["constraints_written"])
        self.assertTrue(payload["dust_closes_conditionally"])
        self.assertFalse(payload["unique_omega_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_assumptions_include_l_transport_and_b4vol(self) -> None:
        assumptions = " ".join(build_payload()["assumptions"])

        self.assertIn("K_plus", assumptions)
        self.assertIn("L_-+", assumptions)
        self.assertIn("Omega_alpha", assumptions)
        self.assertIn("B_4vol", assumptions)

    def test_plus_and_minus_constraints_include_continuity_and_force(self) -> None:
        payload = build_payload()
        plus = {row["name"] for row in payload["plus_constraints"]}
        minus = {row["name"] for row in payload["minus_constraints"]}

        self.assertIn("densitized_continuity", plus)
        self.assertIn("receiver_force", plus)
        self.assertIn("densitized_continuity", minus)
        self.assertIn("receiver_force", minus)

    def test_f_contractions_and_open_items_are_explicit(self) -> None:
        payload = build_payload()
        contractions = " ".join(
            row["f_contraction"]
            for key in ("plus_constraints", "minus_constraints")
            for row in payload[key]
        )
        open_items = " ".join(payload["still_open"])

        self.assertIn("Omega", contractions)
        self.assertIn("D log B_plus", contractions)
        self.assertIn("D log B_minus", contractions)
        self.assertIn("transverse Lorentz gauge", open_items)
        self.assertIn("Q_cross", open_items)


if __name__ == "__main__":
    unittest.main()
