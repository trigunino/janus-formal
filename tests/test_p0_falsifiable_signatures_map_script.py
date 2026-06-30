from __future__ import annotations

import unittest

from scripts.build_p0_falsifiable_signatures_map import build_payload


class P0FalsifiableSignaturesMapScriptTests(unittest.TestCase):
    def test_signatures_gate_closed_but_not_likelihood(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["falsifiable_signature_gate_closed"])
        self.assertFalse(payload["likelihood_pipeline_implemented"])
        self.assertFalse(payload["observable_prediction_ready"])

    def test_lensing_chain_contains_required_rows(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["lensing_chain"]}

        self.assertIn("null_geodesic_bundle", names)
        self.assertIn("ricci_sign", names)
        self.assertIn("weyl_shear_term", names)
        self.assertIn("distance_equation", names)
        self.assertIn("observer_source_gauge", names)

    def test_gw_chain_includes_transition_features(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["gw_chain"]}

        self.assertIn("transfer_matrix", names)
        self.assertIn("frequency_phase_shift", names)
        self.assertIn("mode_mixing", names)
        self.assertIn("blue_red_tilt_correction", names)

    def test_next_step_is_likelihood_pipeline(self) -> None:
        payload = build_payload()
        self.assertEqual(payload["next_gate"], "derive_likelihood_pipeline")
        self.assertEqual(payload["first_next_step"], "derive_likelihood_pipeline")


if __name__ == "__main__":
    unittest.main()
