from __future__ import annotations

import unittest

from scripts.build_p0_eft_minimal_torsion_radion_connection import build_payload, render_markdown


class P0EFTMinimalTorsionRadionConnectionTests(unittest.TestCase):
    def test_ansatz_written_but_not_janus_derived(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["minimal_connection_ansatz_written"])
        self.assertFalse(status["source_derived_from_janus"])
        self.assertFalse(status["heat_kernel_square_done"])
        self.assertFalse(status["prediction_ready"])

    def test_ansatz_names_free_symbols(self) -> None:
        ansatz = build_payload()["ansatz"]

        self.assertIn("q_A", ansatz["free_symbols"])
        self.assertIn("q_T", ansatz["free_symbols"])
        self.assertFalse(ansatz["source_derived"])

    def test_orbifold_even_option_present(self) -> None:
        options = " ".join(row["choice"] for row in build_payload()["projected_options"])

        self.assertIn("orbifold-even paired torsion", options)

    def test_markdown_keeps_warning(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("q_A/q_T are not Janus-derived", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
