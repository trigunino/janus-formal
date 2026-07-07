import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_spectral_stability_exit_gate import build_payload


class ChiLLSpectralStabilityExitGateTests(unittest.TestCase):
    def test_default_blocks_without_operator_inputs(self):
        payload = build_payload(Path("missing-spectral-input.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["spectral_stability_exit_ready"])
        self.assertIn("operator_declared", payload["blocked_by"])
        self.assertIn("R_s_m", payload["blocked_by"])

    def test_forbidden_shortcuts_are_explicit(self):
        shortcuts = build_payload(Path("missing-spectral-input.json"))["forbidden_shortcuts"]

        self.assertTrue(shortcuts["choose_target_eigenvalue_by_observation"])
        self.assertTrue(shortcuts["declare_zero_mode_without_operator_domain"])
        self.assertTrue(shortcuts["select_R_s_without_scale_selection_law"])

    def test_closes_conditionally_with_complete_laplacian_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "spectral.json"
            path.write_text(
                json.dumps(
                    {
                        "operator": "scalar_laplacian_S2_round",
                        "R_s_m": 3.0,
                        "ell_mode": 1,
                        "domain_and_measure_declared": True,
                        "boundary_or_spin_structure_declared": True,
                        "self_adjointness_declared": True,
                        "stability_criterion_declared": True,
                        "scale_selection_law_declared": True,
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["spectral_stability_exit_ready"])
        self.assertAlmostEqual(
            payload["derivation"]["lowest_nonzero_eigenvalue_m_minus_2"],
            2.0 / 9.0,
        )
        self.assertAlmostEqual(
            payload["derivation"]["chi_LL_abs_inverse_m"],
            1.0 / (8.0 * math.pi * 3.0),
        )


if __name__ == "__main__":
    unittest.main()
