from __future__ import annotations

import unittest

from scripts.build_p0_eft_run8_orbifold_euler_characteristic_audit import build_payload, render_markdown


class P0EFTRun8OrbifoldEulerCharacteristicAuditTests(unittest.TestCase):
    def test_euler_cover_interface_is_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run8_euler_cover_interface_ready"])
        self.assertTrue(status["multiplicity_to_ratio_arrow_formalized"])

    def test_multiplicity_proofs_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["branch_locus_multiplicity_computed"])
        self.assertFalse(status["positive_sheet_multiplicity_two_proved"])
        self.assertFalse(status["orbifold_cover_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_target_multiplicity(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("positive sheet 2, negative sheet 1", markdown)
        self.assertIn("coverMultiplicityTwoToOne", markdown)


if __name__ == "__main__":
    unittest.main()
