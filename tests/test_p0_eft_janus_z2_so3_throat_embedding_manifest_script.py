from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_so3_throat_embedding_manifest import build_payload


class Z2SO3ThroatEmbeddingManifestScriptTests(unittest.TestCase):
    def test_manifest_connects_so3_reduction_to_throat_skeleton(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["embedding_family"], "stationary_SO3_projective_throat")
        self.assertTrue(payload["same_sector_attraction_ready"])
        self.assertTrue(payload["opposite_sector_repulsion_ready"])
        self.assertFalse(payload["R_Sigma_solution_certificate_ready"])


if __name__ == "__main__":
    unittest.main()
