from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_beta_field_provenance_gate import build_payload


class P0BetaFieldProvenanceGateTests(unittest.TestCase):
    def test_gate_defined_but_source_derived_beta_unavailable(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["beta_field_gate_defined"])
        self.assertTrue(decision["pm_calibrated_beta_usable_as_diagnostic"])
        self.assertFalse(decision["source_derived_beta_available"])
        self.assertFalse(decision["noncomoving_source_identity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_distinguish_diagnostic_and_source_derived(self) -> None:
        rows = {row["provenance"]: row for row in build_payload()["rows"]}

        self.assertFalse(rows["declared_physical_velocity"]["prediction_ready"])
        self.assertFalse(rows["pm_hubble_calibrated_diagnostic"]["prediction_ready"])
        self.assertTrue(rows["source_derived_janus_dynamics"]["prediction_ready"])

    def test_forbidden_fit_labels_are_listed(self) -> None:
        forbidden = set(build_payload()["forbidden"])

        self.assertIn("shear_fit", forbidden)
        self.assertIn("sigma8_fit", forbidden)
        self.assertIn("s8_fit", forbidden)


if __name__ == "__main__":
    unittest.main()
