from __future__ import annotations

import unittest

from scripts.build_p0_falpha_free_components_gate import build_payload


class P0FalphaFreeComponentsGateTests(unittest.TestCase):
    def test_falpha_gate_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "falpha-free-components-open")
        self.assertTrue(payload["necessary_constraints_written"])
        self.assertFalse(payload["all_falpha_components_source_fixed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_records_determined_and_free_components(self) -> None:
        determined = " ".join(build_payload()["determined_by"])
        free = " ".join(build_payload()["still_free"])

        self.assertIn("Lorentz preservation", determined)
        self.assertIn("receiver force", determined)
        self.assertIn("same-L", determined)
        self.assertIn("transverse", free)
        self.assertIn("off-flow", free)

    def test_closure_requires_source_or_gauge_principle(self) -> None:
        requirements = " ".join(build_payload()["closure_requirements"])

        self.assertIn("source equation or gauge principle", requirements)
        self.assertIn("mirror F_plus/F_minus", requirements)
        self.assertIn("Q_cross", requirements)


if __name__ == "__main__":
    unittest.main()
