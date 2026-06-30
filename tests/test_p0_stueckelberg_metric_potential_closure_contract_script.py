from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_metric_potential_closure_contract import build_payload


class P0MetricPotentialClosureContractTests(unittest.TestCase):
    def test_contract_defined_but_open(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["closure_contract_defined"])
        self.assertFalse(decision["all_conditions_closed"])
        self.assertFalse(decision["poisson_diagnostic_promoted_to_metric"])
        self.assertFalse(payload["prediction_ready"])

    def test_conditions_cover_field_gauge_slip_and_source_identity(self) -> None:
        condition_ids = {row["id"] for row in build_payload()["conditions"]}

        self.assertIn("linearized_field_equation", condition_ids)
        self.assertIn("gauge_lock", condition_ids)
        self.assertIn("slip_relation", condition_ids)
        self.assertIn("source_identity", condition_ids)

    def test_shortcuts_are_forbidden(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("PM Poisson potential", shortcuts)
        self.assertIn("shear, sigma8 or S8", shortcuts)
        self.assertIn("Q_cross or Q_det", shortcuts)
        self.assertIn("a_minus/a_plus", shortcuts)


if __name__ == "__main__":
    unittest.main()
