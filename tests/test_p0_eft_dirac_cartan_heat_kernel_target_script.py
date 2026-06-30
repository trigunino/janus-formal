from __future__ import annotations

import unittest

from scripts.build_p0_eft_dirac_cartan_heat_kernel_target import build_payload, render_markdown


class P0EFTDiracCartanHeatKernelTargetTests(unittest.TestCase):
    def test_target_written_but_not_computed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["dirac_cartan_target_written"])
        self.assertFalse(status["laplace_type_reduction_done"])
        self.assertFalse(status["a4_coefficients_computed"])
        self.assertFalse(status["prediction_ready"])

    def test_a4_sources_include_bulk_and_boundary(self) -> None:
        sources = " ".join(row["term"] for row in build_payload()["a4_sources"])

        self.assertIn("tr(E_C^2)", sources)
        self.assertIn("tr(Omega_C_mn Omega_C^mn)", sources)
        self.assertIn("boundary a4 coefficients", sources)

    def test_no_automatic_double_dual_claim(self) -> None:
        checks = {row["id"]: row for row in build_payload()["checks"]}

        self.assertEqual(checks["DC2"]["status"], "not_proved")
        self.assertEqual(checks["DC3"]["status"], "open")
        self.assertEqual(checks["DC4"]["status"], "open")

    def test_markdown_keeps_inputs_needed(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("explicit torsion/radion connection", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
