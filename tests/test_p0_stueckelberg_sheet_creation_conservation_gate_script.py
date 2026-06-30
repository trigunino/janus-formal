from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sheet_creation_conservation_gate import build_payload


class P0SheetCreationConservationGateTests(unittest.TestCase):
    def test_sheet_creation_defined_but_not_conservation_closed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["sheet_creation_rule_defined"])
        self.assertFalse(decision["conservation_closed"])
        self.assertFalse(decision["new_fit_parameters"])
        self.assertFalse(payload["prediction_ready"])

    def test_conservation_rules_cover_mass_momentum_optics_and_mirror(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["conservation_rules"]}

        self.assertIn("mass_weight_conservation", names)
        self.assertIn("momentum_sheet_balance", names)
        self.assertIn("no_new_lensing_weight", names)
        self.assertIn("mirror_sheet_pairing", names)

    def test_forbidden_rules_block_fits(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden"])

        self.assertIn("fit observations", forbidden)
        self.assertIn("Q_cross amplitude", forbidden)
        self.assertIn("mirror-inconsistent", forbidden)


if __name__ == "__main__":
    unittest.main()
