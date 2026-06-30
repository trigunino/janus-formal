from __future__ import annotations

import unittest

from scripts.build_p0_eft_mass_shell_b4vol_measure import build_payload, render_markdown


class P0EFTMassShellB4volMeasureTests(unittest.TestCase):
    def test_mass_shell_defined_but_b4vol_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["mass_shell_measure_defined"])
        self.assertTrue(status["lapse_energy_factor_identified"])
        self.assertTrue(status["b4vol_candidate_defined"])
        self.assertFalse(status["b4vol_derived_from_soldering"])
        self.assertFalse(status["active_source_measure_closed"])

    def test_b4vol_is_not_dust_volume(self) -> None:
        b4vol = build_payload()["b4vol"]

        self.assertIn("four-volume", b4vol["meaning"])
        self.assertIn("not from dust volume", " ".join(build_payload()["obligations"]))
        self.assertIn("dust 3-volume", b4vol["not_equal_to"])

    def test_measure_names_lapse_energy(self) -> None:
        measures = build_payload()["measures"]

        self.assertIn("p^0", measures["mass_shell"])
        self.assertIn("lapse", measures["lapse_energy"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("b4vol_derived_from_soldering: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
