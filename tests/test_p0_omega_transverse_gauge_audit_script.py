from __future__ import annotations

import unittest

from scripts.build_p0_omega_transverse_gauge_audit import build_payload


class P0OmegaTransverseGaugeAuditTests(unittest.TestCase):
    def test_audit_keeps_unique_omega_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["omega_decomposed"])
        self.assertTrue(payload["dust_does_not_fix_unique_omega"])
        self.assertTrue(payload["gauge_lifting_options_written"])
        self.assertFalse(payload["unique_omega_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_decomposition_lists_visible_and_invisible_dust_parts(self) -> None:
        d = build_payload()["decomposition"]

        self.assertEqual(d["per_alpha_components"], 6)
        self.assertIn("densitized continuity", " ".join(d["dust_visible"]))
        self.assertIn("receiver-force", " ".join(d["dust_visible"]))
        self.assertIn("rest-space rotations", " ".join(d["dust_invisible"]))
        self.assertIn("screen rotations", " ".join(d["dust_invisible"]))

    def test_gauge_lifting_options_include_matter_boundary_and_action(self) -> None:
        options = {row["option"] for row in build_payload()["gauge_lifting_options"]}

        self.assertIn("minimal_rotation", options)
        self.assertIn("anisotropic_Pi_axes", options)
        self.assertIn("boundary_initial_L", options)
        self.assertIn("action_principle_for_L", options)

    def test_qcross_implications_block_lensing_fit(self) -> None:
        text = " ".join(build_payload()["implication_for_qcross"])

        self.assertIn("one photon direction", text)
        self.assertIn("screen rotations", text)
        self.assertIn("do not tune transverse gauge", text)
        self.assertIn("survey comparison", text)


if __name__ == "__main__":
    unittest.main()
