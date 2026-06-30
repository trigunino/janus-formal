from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_transverse_label_caustic_gate import build_payload


class P0TransverseLabelCausticGateTests(unittest.TestCase):
    def test_caustic_free_gate_limits_worldline_branch(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["worldline_branch_domain_limited"])
        self.assertTrue(decision["caustic_free_condition_required"])
        self.assertFalse(decision["full_global_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_gates_include_jacobian_phi_inverse_and_same_l(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["gates"]}

        self.assertIn("transverse_jacobian_nonzero", names)
        self.assertIn("single_valued_phi", names)
        self.assertIn("mirror_inverse_domain", names)
        self.assertIn("same_l_smoothness", names)

    def test_diagnostic_rules_forbid_smoothing_fit(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["diagnostic_rules"])

        self.assertIn("before caustic", rules)
        self.assertIn("multi-stream", rules)
        self.assertIn("fit parameter", rules)


if __name__ == "__main__":
    unittest.main()
