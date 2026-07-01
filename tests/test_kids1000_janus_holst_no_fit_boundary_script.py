from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_no_fit_boundary import build_payload


class KiDS1000JanusHolstNoFitBoundaryTests(unittest.TestCase):
    def test_payload_blocks_prediction_and_freezes_diagnostic_candidate(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "kids1000-janus-holst-no-fit-boundary-active")
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim_allowed"])
        self.assertEqual(payload["dominant_failure"]["pair"], "2-3")
        self.assertTrue(any("bin-2 delta_z" in item for item in payload["forbidden_uses"]))
        self.assertGreater(len(payload["open_gates"]), 0)


if __name__ == "__main__":
    unittest.main()
