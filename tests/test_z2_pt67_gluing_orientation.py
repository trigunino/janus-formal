from __future__ import annotations

import unittest

from src.janus_lab.z2_pt67_gluing_orientation import (
    pt67_gluing_orientation_payload,
)


class Z2PT67GluingOrientationTests(unittest.TestCase):
    def test_pt_transport_makes_extrinsic_curvature_invariant(self) -> None:
        payload = pt67_gluing_orientation_payload()

        self.assertTrue(payload["input_regular_surface_ready"])
        self.assertEqual(payload["DeltaK_PT_transport"]["DeltaK_TT"], 0.0)
        self.assertEqual(payload["DeltaK_PT_transport"]["DeltaK_thetatheta"], 0.0)
        self.assertTrue(payload["DeltaK_PT_transport"]["DeltaK_ready"])

    def test_raccord_uses_no_free_orientation_sign(self) -> None:
        payload = pt67_gluing_orientation_payload()

        self.assertTrue(payload["not_using"]["free_orientation_sign"])
        self.assertTrue(payload["not_using"]["outward_Israel_cut_and_paste_normals"])
        self.assertTrue(payload["raccord_to_regular_sigma_pipeline"]["DeltaK_PT_transport_ready"])


if __name__ == "__main__":
    unittest.main()
