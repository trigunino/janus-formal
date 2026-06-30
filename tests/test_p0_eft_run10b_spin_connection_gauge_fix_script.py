from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_spin_connection_gauge_fix import build_payload, render_markdown


class P0EFTRun10BSpinConnectionGaugeFixTests(unittest.TestCase):
    def test_gauge_fix_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_spin_connection_gauge_fix_ready"])
        self.assertTrue(status["spin_connection_gauge_fixed_on_cycle_proved"])
        self.assertTrue(status["spin_connection_restricts_to_orbifold_cycle_proved"])

    def test_flux_locks_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["holonomy_quantum_normalized_proved"])
        self.assertFalse(status["normalized_flux_integer_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_gauge_fix(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldSpinConnectionGaugeFix", markdown)
        self.assertIn("spinConnectionGaugeFixedOnCycle", markdown)
        self.assertIn("fluxQuantizationLawClosed", markdown)


if __name__ == "__main__":
    unittest.main()
