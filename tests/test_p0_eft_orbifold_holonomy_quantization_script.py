from __future__ import annotations

import unittest

from scripts.build_p0_eft_orbifold_holonomy_quantization import build_payload, render_markdown


class P0EFTOrbifoldHolonomyQuantizationTests(unittest.TestCase):
    def test_a_sigma_identity_closes_under_volume_quantum(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["derivation"]["a_sigma"], "2/3")
        self.assertEqual(payload["derivation"]["z_sigma"], "1/2")
        self.assertEqual(payload["derivation"]["identity_residual_3a_sigma_minus_2"], "0")
        self.assertTrue(
            payload["theorem_status"][
                "a_sigma_identity_closed_under_holonomy_volume_quantum"
            ]
        )

    def test_volume_quantum_remains_explicit_input(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["volume_quantum_still_an_input"])
        self.assertFalse(status["no_fit_lock_ready_from_a_sigma_alone"])

    def test_markdown_names_membrane_lock(self) -> None:
        self.assertIn("a_sigma=2/3", render_markdown(build_payload()))


if __name__ == "__main__":
    unittest.main()
