from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_lensing_observable_chain_gate import build_payload


class P0LensingObservableChainGateTests(unittest.TestCase):
    def test_lensing_chain_defined_but_not_prediction_ready(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["observable_chain_defined"])
        self.assertTrue(decision["diagnostic_outputs_defined"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_includes_shear_distance_and_gauge(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["chain"]}

        self.assertIn("weyl_shear", names)
        self.assertIn("angular_diameter_distance", names)
        self.assertIn("gauge_observer_source", names)

    def test_outputs_keep_qdet_qcross_and_sign_explicit(self) -> None:
        payload = build_payload()
        outputs = " ".join(payload["output_columns"])

        self.assertIn("janus_cross_sign_status", outputs)
        self.assertIn("qdet_separate", outputs)
        self.assertIn("qcross_reduced_sachs", outputs)


if __name__ == "__main__":
    unittest.main()
