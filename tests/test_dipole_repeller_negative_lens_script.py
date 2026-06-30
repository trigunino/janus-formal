from __future__ import annotations

import unittest

from scripts.diagnose_dipole_repeller_negative_lens import build_payload


class DipoleRepellerNegativeLensScriptTests(unittest.TestCase):
    def test_profile_has_expected_shape_checks(self) -> None:
        payload = build_payload()

        self.assertTrue(all(payload["checks"].values()))
        self.assertEqual(payload["status"], "shape-diagnostic-not-survey-fit")


if __name__ == "__main__":
    unittest.main()
