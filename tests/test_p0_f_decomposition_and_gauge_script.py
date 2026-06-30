from __future__ import annotations

import unittest

from scripts.build_p0_f_decomposition_and_gauge import build_payload


class P0FDecompositionAndGaugeTests(unittest.TestCase):
    def test_decomposition_keeps_f_non_unique(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["omega_decomposition_written"])
        self.assertTrue(payload["dust_constraints_identified"])
        self.assertTrue(payload["gauge_freedom_remaining"])
        self.assertFalse(payload["unique_f_from_dust"])
        self.assertFalse(payload["prediction_ready"])

    def test_omega_is_eta_antisymmetric_with_six_components(self) -> None:
        decomposition = build_payload()["decomposition"]
        text = " ".join(decomposition["split"])

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", decomposition["object"])
        self.assertIn("Omega_{alpha AB}=-Omega_{alpha BA}", decomposition["lorentz_constraint"])
        self.assertEqual(decomposition["components_per_alpha"], 6)
        self.assertIn("3 boost", text)
        self.assertIn("3 spatial rotation", text)

    def test_dust_constraints_do_not_fix_transverse_rotations(self) -> None:
        parts = " ".join(row["does_not_fix"] for row in build_payload()["dust_fixed_parts"])

        self.assertIn("spatial rotations", parts)
        self.assertIn("trace-free transverse", parts)
        self.assertIn("screen-plane rotations", parts)

    def test_gauge_candidates_are_not_source_derived(self) -> None:
        candidates = build_payload()["gauge_candidates"]

        self.assertTrue(all("not source-derived" in row["status"] or "diagnostic" in row["status"] for row in candidates))
        self.assertTrue(any(row["name"] == "fermi_walker_minimal_rotation" for row in candidates))
        self.assertTrue(any(row["name"] == "polar_lorentz_minimal_strain" for row in candidates))

    def test_higher_matter_tensors_are_needed_for_full_transport(self) -> None:
        implications = " ".join(build_payload()["closure_implications"])

        self.assertIn("perfect-fluid pressure", implications)
        self.assertIn("anisotropic stress Pi", implications)
        self.assertIn("dust closure alone cannot uniquely determine", implications)


if __name__ == "__main__":
    unittest.main()
