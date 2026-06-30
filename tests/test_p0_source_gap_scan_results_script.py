from __future__ import annotations

import unittest

from scripts.build_p0_source_gap_scan_results import build_payload


class P0SourceGapScanResultsTests(unittest.TestCase):
    def test_scan_confirms_no_source_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["local_library_scanned"])
        self.assertFalse(payload["f_alpha_source_found"])
        self.assertFalse(payload["dlogb_cancellation_source_found"])
        self.assertFalse(payload["closure_allowed_from_sources"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_blocker_scans_are_recorded(self) -> None:
        targets = {row["target"] for row in build_payload()["scans"]}

        self.assertIn("L_minus_to_plus / D_alpha L / F_alpha", targets)
        self.assertIn("D log B_4vol cancellation / Bianchi product-rule identities", targets)

    def test_closest_anchors_keep_closure_disallowed(self) -> None:
        payload = build_payload()

        self.assertTrue(all(row["result"] == "not-found" for row in payload["scans"]))
        self.assertTrue(all(not row["closure_allowed"] for row in payload["scans"]))
        anchors = " ".join(anchor for row in payload["scans"] for anchor in row["closest_anchors"])
        self.assertIn("source_traceability.md", anchors)
        self.assertIn("M15", anchors)
        self.assertIn("M30", anchors)

    def test_consequences_require_derivation_or_axiom(self) -> None:
        consequences = " ".join(build_payload()["consequences"])

        self.assertIn("new work", consequences)
        self.assertIn("axiom branch", consequences)
        self.assertIn("R_plus/R_minus", consequences)
        self.assertIn("diagnostic_pm_only", consequences)


if __name__ == "__main__":
    unittest.main()
