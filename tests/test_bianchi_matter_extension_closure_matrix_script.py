from __future__ import annotations

import unittest

from scripts.build_bianchi_matter_extension_closure_matrix import build_payload


class BianchiMatterExtensionClosureMatrixTests(unittest.TestCase):
    def test_dust_perfect_fluid_and_anisotropic_cases_are_tracked(self) -> None:
        rows = {row["case"]: row for row in build_payload()["rows"]}

        self.assertIn("dust", rows)
        self.assertIn("perfect_fluid_flrw_scalar", rows)
        self.assertIn("anisotropic_stress", rows)

    def test_no_matter_case_is_marked_closed(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["all_matter_cases_closed"])
        self.assertTrue(all(not row["closed"] for row in payload["rows"]))

    def test_anisotropic_stress_cannot_use_scalar_shortcut(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])

        self.assertIn("do not reuse scalar perfect-fluid branch", forbidden)
        self.assertIn("do not merge pressure or Pi into Q_cross", forbidden)


if __name__ == "__main__":
    unittest.main()
