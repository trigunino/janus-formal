import json
import tempfile
import unittest
from pathlib import Path

from tests.test_p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate_script import (
    _embedding_manifest,
)

from scripts.build_p0_eft_janus_z2_sigma_plugstar_curvature_amplitude_from_embedding_gate import (
    build_payload,
    derive_active_a_k,
)


class PlugstarCurvatureAmplitudeFromEmbeddingGateTests(unittest.TestCase):
    def test_derives_a_k_from_active_rsigma_and_k_grid(self):
        embedding = _embedding_manifest(include_k=True)
        embedding["R_Sigma_of_a"] = [2.0, 3.0]
        k_payload = {
            "K_s_plus_Z2Sigma": [0.5, 1.0],
            "K_s_minus_Z2Sigma": [0.25, 0.5],
            "K_tau_plus_Z2Sigma": [1.0, 2.0],
            "K_tau_minus_Z2Sigma": [0.5, 1.0],
        }

        result = derive_active_a_k(embedding, k_payload)

        self.assertAlmostEqual(result["rows"][0]["C_K_plus"], 1.75)
        self.assertAlmostEqual(result["rows"][1]["C_K_plus"], 7.0)
        self.assertAlmostEqual(result["A_K"], 63.0)
        self.assertIn("3*K_s", result["curvature_concentration_formula"])

    def test_build_payload_closes_with_active_embedding_k_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "embedding.json"
            output_path = root / "flrw_k.json"
            payload = _embedding_manifest(include_k=True)
            payload["R_Sigma_of_a"] = [2.0, 3.0]
            payload["K_s_plus_Z2Sigma"] = [0.5, 1.0]
            payload["K_s_minus_Z2Sigma"] = [0.25, 0.5]
            payload["K_tau_plus_Z2Sigma"] = [1.0, 2.0]
            payload["K_tau_minus_Z2Sigma"] = [0.5, 1.0]
            input_path.write_text(json.dumps(payload), encoding="utf-8")

            result = build_payload(embedding_input_path=input_path, k_output_path=output_path)

        self.assertTrue(result["gate_passed"])
        self.assertEqual(result["route_status"], "active_A_K_derived")
        self.assertEqual(result["primary_blocker"], "none")
        self.assertAlmostEqual(result["active_A_K_certificate"]["A_K"], 63.0)
        self.assertIn("sqrt(63", result["threshold_solution"]["active_bound"])
        self.assertEqual(
            result["archive_decision"]["archive_status"],
            "ready_to_archive_with_active_A_K_certificate",
        )
        self.assertFalse(result["archive_decision"]["active_pipeline_import_forbidden"])

    def test_default_payload_blocks_without_active_embedding_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = build_payload(
                embedding_input_path=Path(tmp) / "missing.json",
                k_output_path=Path(tmp) / "flrw_k.json",
            )

        self.assertFalse(result["gate_passed"])
        self.assertEqual(result["route_status"], "blocked_waiting_for_active_embedding_K_grid")
        self.assertIn("FLRW_K_grid_available", result["blockers"])
        self.assertEqual(
            result["archive_decision"]["archive_status"],
            "ready_to_archive_with_blocker",
        )
        self.assertTrue(result["archive_decision"]["does_not_write_fake_active_manifest"])


if __name__ == "__main__":
    unittest.main()
