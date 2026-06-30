from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_rkin_pushforward_derivation import build_payload


class P0RkinPushforwardDerivationTests(unittest.TestCase):
    def test_rkin_is_commutator_shape_not_closure(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["rkin_shape_derived"])
        self.assertFalse(decision["fit_used"])
        self.assertFalse(decision["source_derived_transport_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_contains_liouville_pushforward_commutator(self) -> None:
        payload = build_payload()
        formulas = " ".join(row["formula"] for row in payload["derivation"])

        self.assertIn("L_minus[f_minus]", formulas)
        self.assertIn("Phi_* f_minus", formulas)
        self.assertIn("L_plus Phi_* - Phi_* L_minus", formulas)

    def test_mirror_remains_required(self) -> None:
        payload = build_payload()

        self.assertIn("R_kin,-", payload["mirror"]["formula"])
        self.assertFalse(payload["mirror"]["closed"])


if __name__ == "__main__":
    unittest.main()
