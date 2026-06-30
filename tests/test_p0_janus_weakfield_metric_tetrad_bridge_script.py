from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_metric_tetrad_bridge import build_payload


class P0JanusWeakfieldMetricTetradBridgeTests(unittest.TestCase):
    def test_bridge_is_open_without_source_potentials(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-metric-tetrad-bridge-open")
        self.assertTrue(payload["weakfield_metric_branch_written"])
        self.assertTrue(payload["metric_to_tetrad_closed_at_linear_order"])
        self.assertTrue(payload["tetrad_to_connection_closed_at_linear_order"])
        self.assertFalse(payload["janus_source_potentials_derived"])
        self.assertFalse(payload["determinant_density_convention_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_metric_branch_contains_plus_minus_phi_psi_tetrads(self) -> None:
        text = " ".join(row["metric"] + row["tetrad"] for row in build_payload()["metric_branch"])

        self.assertIn("Phi_plus", text)
        self.assertIn("Psi_plus", text)
        self.assertIn("Phi_minus", text)
        self.assertIn("Psi_minus", text)
        self.assertIn("e_plus^0", text)
        self.assertIn("e_minus^i", text)

    def test_source_targets_require_janus_equations_no_fit(self) -> None:
        payload = build_payload()
        targets = " ".join(payload["source_equation_targets"])

        self.assertIn("Janus weak-field Poisson row", targets)
        self.assertIn("spatial/slip row", targets)
        self.assertIn("determinant convention", targets)
        self.assertIn("without observational fit", targets)
        self.assertFalse(payload["uses_observational_fit"])

    def test_bridge_chain_keeps_source_step_open(self) -> None:
        chain = {row["step"]: row for row in build_payload()["bridge_chain"]}

        self.assertFalse(chain["source_to_metric"]["closed"])
        self.assertTrue(chain["metric_to_tetrad"]["closed"])
        self.assertTrue(chain["tetrad_to_connection"]["closed"])
        self.assertFalse(chain["connection_to_integrability"]["closed"])


if __name__ == "__main__":
    unittest.main()
