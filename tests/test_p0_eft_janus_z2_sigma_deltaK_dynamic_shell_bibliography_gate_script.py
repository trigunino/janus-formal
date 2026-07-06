from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_deltaK_dynamic_shell_bibliography_gate import (
    build_payload,
    render_markdown,
)


class DeltaKDynamicShellBibliographyGateTests(unittest.TestCase):
    def test_bibliography_supports_deltaK_but_not_janus_f_pm(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["deltaK_formula_supported"])
        self.assertTrue(payload["momentum_flux_formula_supported"])
        self.assertFalse(payload["Janus_specific_f_pm_derived"])

    def test_sources_include_key_dynamic_shell_references(self) -> None:
        ids = {row["id"] for row in build_payload()["sources"]}

        self.assertIn("poisson-visser-1995", ids)
        self.assertIn("lobo-crawford-2005", ids)
        self.assertIn("sahu-2024", ids)

    def test_markdown_reports_f_pm_blocker(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("DeltaK Dynamic Shell", markdown)
        self.assertIn("Janus-specific f_pm derived: `False`", markdown)


if __name__ == "__main__":
    unittest.main()
