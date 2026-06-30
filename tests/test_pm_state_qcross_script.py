from __future__ import annotations

import unittest

from scripts.diagnose_pm_state_qcross import build_payload


class PMStateQCrossScriptTests(unittest.TestCase):
    def test_payload_reports_finite_qcross_from_negative_pm_velocities(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["negative_particle_count"], 8)
        self.assertGreater(payload["q_cross_stats"]["min"], 0.0)
        self.assertLess(payload["negative_speed_km_s_stats"]["max"], 300.0)
        self.assertEqual(len(payload["rows"]), 4)


if __name__ == "__main__":
    unittest.main()
