from __future__ import annotations

import unittest

from src.janus_lab.z2_so3_throat_embedding import (
    so3_throat_embedding_manifest,
    so3_throat_stencil,
)


class Z2SO3ThroatEmbeddingTests(unittest.TestCase):
    def test_stencil_has_even_radius_and_odd_first_derivative(self) -> None:
        left, center, right = so3_throat_stencil()

        self.assertAlmostEqual(left["R"], right["R"])
        self.assertAlmostEqual(left["partial_rho_R"], -right["partial_rho_R"])
        self.assertEqual(center["partial_rho_R"], 0.0)
        self.assertGreater(center["partial2_rho_R"], 0.0)

    def test_manifest_is_skeleton_not_delta_k(self) -> None:
        payload = so3_throat_embedding_manifest()

        self.assertTrue(payload["active_embedding_skeleton_ready"])
        self.assertTrue(payload["SO3_reduced_bianchi_ready"])
        self.assertFalse(payload["metric_functions_ready"])
        self.assertFalse(payload["DeltaK_s_tau_ready"])
        self.assertIn("not DeltaK_s or DeltaK_tau", payload["non_claims"])


if __name__ == "__main__":
    unittest.main()
