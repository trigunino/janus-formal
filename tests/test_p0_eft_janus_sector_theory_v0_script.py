import unittest

from scripts.build_p0_eft_janus_sector_theory_v0_matrix import build_payload as build_matrix
from scripts.run_p0_eft_janus_sector_theory_v0_observation_smoke import (
    build_payload as build_observation,
)


class JanusAlphaSectorTheoryTests(unittest.TestCase):
    def test_matrix_keeps_no_fit_alpha_closed(self):
        payload = build_matrix()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertTrue(payload["magic_fit_forbidden"])
        self.assertTrue(any(row["id"] == "published_sn_q0_sector" for row in payload["sector_laws"]))

    def test_observation_smoke_is_sector_selection_not_no_fit(self):
        payload = build_observation()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertEqual(payload["paper_q0"], -0.087)
        self.assertIn("q0", payload["primary_best"])
        self.assertIn("sector", payload["interpretation"])


if __name__ == "__main__":
    unittest.main()
