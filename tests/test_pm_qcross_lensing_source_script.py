from __future__ import annotations

import unittest

from scripts.diagnose_pm_qcross_lensing_source import build_payload


class PMQCrossLensingSourceScriptTests(unittest.TestCase):
    def test_qcross_weighted_source_has_nonzero_diagnostic_delta(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["q_cross_stats"]["min"], 0.0)
        self.assertGreater(payload["source_delta_stats"]["std"], 0.0)
        self.assertLess(payload["centered_qcross_source_stats"]["min"], 0.0)
        self.assertGreater(payload["centered_qcross_source_stats"]["max"], 0.0)


if __name__ == "__main__":
    unittest.main()
