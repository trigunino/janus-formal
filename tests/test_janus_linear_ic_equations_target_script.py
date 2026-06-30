from __future__ import annotations

import unittest

from scripts.build_janus_linear_ic_equations_target import build_payload


class JanusLinearICEquationsTargetTests(unittest.TestCase):
    def test_ic_targets_share_one_linear_operator(self) -> None:
        payload = build_payload()
        targets = {row["target"] for row in payload["derived_targets"]}
        equations = {row["name"] for row in payload["equations"]}

        self.assertFalse(payload["physics_closed"])
        self.assertEqual(targets, {"transfer", "growth", "velocity", "amplitude"})
        self.assertIn("positive_effective_poisson", equations)
        self.assertIn("negative_potential", equations)
        self.assertIn("euler_plus", equations)
        self.assertIn("euler_minus", equations)
        self.assertTrue(any("E_J" in item for item in payload["growth_targets"]))
        self.assertTrue(any("theta_s" in item for item in payload["velocity_targets"]))

    def test_no_sigma8_fit_substitute_is_allowed(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])
        controls = " ".join(payload["numerical_controls"])

        self.assertIn("without fitting sigma8", blockers)
        self.assertIn("L_minus_to_plus", blockers)
        self.assertIn("fixed-total mass normalization", controls)
        self.assertIn("not a physical Janus transfer function", controls)
        self.assertTrue(any("A_J" in item for item in payload["transfer_boundary"]))


if __name__ == "__main__":
    unittest.main()
