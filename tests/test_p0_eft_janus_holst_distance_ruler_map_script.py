from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_holst_distance_ruler_map import build_payload


class P0EFTJanusHolstDistanceRulerMapTests(unittest.TestCase):
    def test_distance_ruler_targets_are_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-holst-late-distance-map-derived-sound-ruler-open")
        self.assertTrue(payload["late_distance_targets_ready"])
        self.assertTrue(payload["bao_shape_diagnostic_unblocked"])
        self.assertFalse(payload["bao_likelihood_unblocked"])
        self.assertFalse(payload["cmb_likelihood_unblocked"])

    def test_required_targets_cover_bao_and_cmb(self) -> None:
        names = {row["name"] for row in build_payload()["targets"]}

        self.assertIn("D_H(z)", names)
        self.assertIn("D_M(z)", names)
        self.assertIn("r_star_or_r_d", names)
        self.assertIn("theta_star", names)

    def test_distance_samples_are_finite(self) -> None:
        for row in build_payload()["sample_distances"]:
            self.assertGreaterEqual(row["z"], 0.0)
            self.assertGreater(row["E"], 0.0)
            self.assertGreater(row["D_H_unit"], 0.0)

    def test_forbids_lcdm_shortcuts(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("LambdaCDM", shortcuts)
        self.assertIn("LCDM H(z)", shortcuts)


if __name__ == "__main__":
    unittest.main()
