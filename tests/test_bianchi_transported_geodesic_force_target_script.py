from __future__ import annotations

import unittest

from scripts.build_bianchi_transported_geodesic_force_target import build_payload


class BianchiTransportedGeodesicForceTargetTests(unittest.TestCase):
    def test_force_cancellation_is_equivalent_target_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["force_cancellation_equivalent_to_receiver_geodesic"])
        self.assertFalse(payload["receiver_geodesics_source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_receiver_geodesic_targets_are_present(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["transported_geodesic_targets"]}

        self.assertIn("D_plus_nu u_{-to+}", rows["negative_to_positive"]["target"])
        self.assertIn("+ C^mu_{nu a}", rows["negative_to_positive"]["equivalent_force"])
        self.assertIn("D_minus_nu u_{+to-}", rows["positive_to_negative"]["target"])
        self.assertIn("- C^mu_{nu a}", rows["positive_to_negative"]["equivalent_force"])

    def test_same_sector_geodesic_shortcut_is_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("same-sector geodesic does not imply", forbidden)
        self.assertIn("do not drop C terms", forbidden)


if __name__ == "__main__":
    unittest.main()
