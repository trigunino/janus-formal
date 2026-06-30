from __future__ import annotations

import unittest

from scripts.build_p0_receiver_geodesic_transport_derivation import build_payload


class P0ReceiverGeodesicTransportDerivationTests(unittest.TestCase):
    def test_own_geodesics_are_anchored_but_receiver_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["own_geodesics_source_anchored"])
        self.assertFalse(payload["receiver_geodesics_derived"])
        self.assertTrue(payload["expanded_l_conditions_written"])
        self.assertFalse(payload["fermi_walker_derives_receiver_flow"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_transport_directions_have_receiver_geodesics(self) -> None:
        rows = {row["direction"]: row for row in build_payload()["transported_geodesics"]}

        self.assertIn("D_plus", rows["negative_to_positive"]["receiver_geodesic"])
        self.assertIn("F_-+", rows["negative_to_positive"]["expanded_l_condition"])
        self.assertIn("+ C^A_{BC}", rows["negative_to_positive"]["connection_form"])
        self.assertIn("D_minus", rows["positive_to_negative"]["receiver_geodesic"])
        self.assertIn("F_+-", rows["positive_to_negative"]["expanded_l_condition"])
        self.assertIn("- C^A_{BC}", rows["positive_to_negative"]["connection_form"])

    def test_status_distinguishes_own_from_receiver_geodesics(self) -> None:
        status = " ".join(build_payload()["derivation_status"])

        self.assertIn("own-sector Janus geodesics", status)
        self.assertIn("stronger conditions", status)
        self.assertIn("F must supply", status)
        self.assertIn("does not derive that flow", status)

    def test_forbidden_shortcuts_block_local_boost_and_qcross_fit(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not replace receiver-geodesic", forbidden)
        self.assertIn("local Lorentz boost", forbidden)
        self.assertIn("fitted Q_cross", forbidden)


if __name__ == "__main__":
    unittest.main()
