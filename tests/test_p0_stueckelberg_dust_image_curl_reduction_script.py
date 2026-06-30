from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dust_image_curl_reduction import build_payload


class P0DustImageCurlReductionTests(unittest.TestCase):
    def test_worldline_integrability_reduces_but_does_not_close_global_curls(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["dust_worldline_integrability_reduced"])
        self.assertFalse(decision["full_curl_integrability_closed"])
        self.assertTrue(decision["diagnostic_ode_branch_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_remaining_obstructions_include_transverse_and_same_l(self) -> None:
        payload = build_payload()
        obstructions = " ".join(payload["remaining_obstructions"])

        self.assertIn("transverse gradients", obstructions)
        self.assertIn("same-L", obstructions)
        self.assertIn("pressure/Pi", obstructions)

    def test_reduction_is_worldline_only(self) -> None:
        payload = build_payload()
        closes = [row["closes"] for row in payload["reductions"]]

        self.assertIn("worldline-only", closes)
        self.assertIn(False, closes)


if __name__ == "__main__":
    unittest.main()
