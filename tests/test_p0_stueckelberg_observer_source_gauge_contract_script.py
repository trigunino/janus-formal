from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_observer_source_gauge_contract import build_payload


class P0ObserverSourceGaugeContractTests(unittest.TestCase):
    def test_gauge_contract_defined_but_not_survey_ready(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["gauge_contract_defined"])
        self.assertFalse(decision["survey_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_contract_contains_tetrad_redshift_affine_and_map(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["contract"]}

        self.assertIn("observer_tetrad", names)
        self.assertIn("source_redshift", names)
        self.assertIn("affine_scale", names)
        self.assertIn("map_convention", names)

    def test_forbidden_blocks_hidden_calibration(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden"])

        self.assertIn("fitted redshift", forbidden)
        self.assertIn("calibration multiplier", forbidden)
        self.assertIn("switching tetrads", forbidden)


if __name__ == "__main__":
    unittest.main()
