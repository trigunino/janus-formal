from __future__ import annotations

import unittest

from scripts.diagnose_quantum_janus_1d import build_payload


class QuantumJanusDiagnosticScriptTests(unittest.TestCase):
    def test_payload_compares_janus_free_and_control(self) -> None:
        payload = build_payload(steps=4, dt=0.02, gravitational_constant=0.05)
        rows = {row["mode"]: row for row in payload["rows"]}

        self.assertIn("free", rows)
        self.assertIn("janus_schrodinger_poisson", rows)
        self.assertIn("all_attractive_control", rows)
        self.assertGreater(rows["janus_schrodinger_poisson"]["delta_separation"], 0.0)
        self.assertLess(rows["all_attractive_control"]["delta_separation"], 0.0)
        self.assertAlmostEqual(rows["free"]["delta_separation"], 0.0)
        self.assertTrue(payload["passed"])

    def test_boundary_states_diagnostic_scope(self) -> None:
        payload = build_payload(steps=1, dt=0.01, gravitational_constant=0.01)

        self.assertIn("Diagnostic only", payload["boundary"])
        self.assertIn("frozen-potential", payload["boundary"])


if __name__ == "__main__":
    unittest.main()
