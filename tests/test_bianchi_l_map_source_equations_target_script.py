from __future__ import annotations

import unittest

from scripts.build_bianchi_l_map_source_equations_target import build_payload


class BianchiLMapSourceEquationsTargetTests(unittest.TestCase):
    def test_l_maps_are_targets_not_predictions(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["differential_transport_derived"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_distinguishes_raw_l_geom_from_admissible_l_maps(self) -> None:
        payload = build_payload()
        definitions = payload["l_map_definitions"]
        requirements = " ".join(payload["admissibility_requirements"])
        forbidden = " ".join(payload["forbidden_shortcuts"])

        self.assertIn("L_geom=e_plus E_minus", definitions["raw_L_geom"])
        self.assertIn("L_minus_to_plus^T eta L_minus_to_plus=eta", requirements)
        self.assertIn("L_plus_to_minus^T eta L_plus_to_minus=eta", requirements)
        self.assertIn("L_geom^T eta L_geom=eta", forbidden)

    def test_differential_transport_targets_dl_terms(self) -> None:
        equations = " ".join(build_payload()["differential_transport_equations"])

        self.assertIn("D_alpha L_minus_to_plus", equations)
        self.assertIn("D_alpha L_plus_to_minus", equations)
        self.assertIn("positive residual force", equations)
        self.assertIn("negative residual force", equations)

    def test_same_l_maps_induce_m_and_k_for_bianchi(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["induced_transport_requirements"])
        residuals = " ".join(payload["residual_closure_requirements"])

        self.assertIn("same L_minus_to_plus", requirements)
        self.assertIn("M_minus_to_plus", requirements)
        self.assertIn("K_plus", requirements)
        self.assertIn("same L_plus_to_minus", requirements)
        self.assertIn("M_plus_to_minus", requirements)
        self.assertIn("K_minus", requirements)
        self.assertIn("R_plus^mu=0 and R_minus^mu=0", residuals)

    def test_unresolved_inputs_keep_p0_open(self) -> None:
        payload = build_payload()
        unresolved = " ".join(payload["unresolved_inputs"])
        verdict = payload["verdict"]

        self.assertIn("derive F_minus_to_plus and F_plus_to_minus", unresolved)
        self.assertIn("not a Janus derivation yet", verdict)
        self.assertFalse(payload["physics_closed"])


if __name__ == "__main__":
    unittest.main()
