import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_irreducible_torsion_pullback_gate import (
    build_payload,
)


class FLRWIrreducibleTorsionPullbackGateTests(unittest.TestCase):
    def test_default_blocks_on_sigma_torsion_pullback(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "Sigma_torsion_pullback")
        self.assertIn("Sigma_torsion_pullback_ready = false", payload["current_frontier"])

    def test_requires_all_irreducible_components_after_sigma_pullback(self):
        payload = build_payload(sigma_torsion_pullback_ready=True)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "trace_vector_torsion_component")
        self.assertIn("axial_vector_component_ready = false", payload["current_frontier"])

    def test_passes_with_active_irreducible_components(self):
        payload = build_payload(
            sigma_torsion_pullback_ready=True,
            irreducible_components_payload={
                "trace_vector_component_ready": True,
                "axial_vector_component_ready": True,
                "tensor_torsion_component_ready": True,
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["FLRW_irreducible_torsion_pullback_ready"])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_reads_active_component_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "components.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "archived_z4_background_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "observational_H0_fit_used": False,
                        "observational_curvature_fit_used": False,
                        "trace_vector_component_ready": True,
                        "axial_vector_component_ready": True,
                        "tensor_torsion_component_ready": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(sigma_torsion_pullback_ready=True, components_path=path)

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
