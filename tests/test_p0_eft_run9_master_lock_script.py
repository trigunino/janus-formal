from __future__ import annotations

import unittest

from scripts.build_p0_eft_run9_master_lock import build_payload, render_markdown


class P0EFTRun9MasterLockTests(unittest.TestCase):
    def test_scaffold_complete_but_no_fit_false(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["global_topology_scaffold_complete"])
        self.assertTrue(status["run10b_orbifold_flux_integer_interface_ready"])
        self.assertTrue(status["run10b_singular_cycle_represents_z2_generator_proved"])
        self.assertTrue(status["run10b_holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertTrue(status["run10b_spin_connection_gauge_fixed_on_cycle_proved"])
        self.assertTrue(status["run10b_holonomy_quantum_normalized_proved"])
        self.assertTrue(status["run10b_normalized_flux_integer_proved"])
        self.assertTrue(status["run10b_integer_flux_law_proved"])
        self.assertTrue(status["run10b_janus_orientation_rule_proved"])
        self.assertTrue(status["full_cosmology_prediction_ready_conditionally"])
        self.assertTrue(status["aps_global_theorem_proved"])
        self.assertTrue(status["orbifold_global_theorem_proved"])
        self.assertTrue(status["full_cosmology_prediction_ready_no_fit"])

    def test_both_axes_are_present(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["run7_aps_axis"]["status"], "scaffold complete")
        self.assertEqual(
            payload["run7_aps_axis"]["global_index_closure_module"],
            "P0EFTAPSPinGlobalIndexClosure",
        )
        self.assertEqual(payload["run8_orbifold_axis"]["status"], "scaffold complete")
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_integer_flux_module"],
            "P0EFTOrbifoldFluxIntegerTheorem",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_orientation_module"],
            "P0EFTOrbifoldFluxOrientationRule",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_flux_quantization_law_module"],
            "P0EFTOrbifoldFluxQuantizationLaw",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_holonomy_normalization_module"],
            "P0EFTOrbifoldHolonomyQuantumNormalization",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_z2_holonomy_unit_module"],
            "P0EFTOrbifoldZ2HolonomyUnit",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_z2_group_law_module"],
            "P0EFTOrbifoldZ2GroupLaw",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_singular_cycle_generator_module"],
            "P0EFTOrbifoldSingularCycleGenerator",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_generator_holonomy_unit_module"],
            "P0EFTOrbifoldGeneratorHolonomyUnit",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_spin_connection_gauge_fix_module"],
            "P0EFTOrbifoldSpinConnectionGaugeFix",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_holonomy_quantum_normalized_module"],
            "P0EFTOrbifoldHolonomyQuantumNormalized",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_normalized_flux_integer_module"],
            "P0EFTOrbifoldNormalizedFluxInteger",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_integer_flux_law_module"],
            "P0EFTOrbifoldIntegerFluxLaw",
        )
        self.assertEqual(
            payload["run8_orbifold_axis"]["run10b_janus_orientation_rule_module"],
            "P0EFTOrbifoldJanusOrientationRule",
        )

    def test_report_names_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("proved_local", markdown)
        self.assertIn("proved_global", markdown)
        self.assertNotIn("postulated_global", markdown)


if __name__ == "__main__":
    unittest.main()
