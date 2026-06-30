from __future__ import annotations

import unittest

from scripts.build_p0_dust_densitized_current_density_response import build_payload


class P0DustDensitizedCurrentDensityResponseTests(unittest.TestCase):
    def test_densitized_current_branch_closed_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "densitized-current-density-response-closed-branch-only")
        self.assertTrue(payload["densitized_current_branch_closed"])
        self.assertFalse(payload["fixed_vector_current_branch_closed"])
        self.assertFalse(payload["janus_pullback_branch_closed"])
        self.assertTrue(payload["pullback_density_response_bridge_available"])
        self.assertFalse(payload["index_convention_locked"])
        self.assertFalse(payload["full_dust_delta_g_t_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_contains_measure_and_pullback_warning(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["derivation_rows"])

        self.assertIn("J^mu", text)
        self.assertIn("sqrt(-g)", text)
        self.assertIn("delta_g rho", text)
        self.assertIn("B_4vol/J_phi", text)
        self.assertIn("index-convention-required", text)


if __name__ == "__main__":
    unittest.main()
