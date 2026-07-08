import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_bulk_observable_path_gate import (
    build_payload,
)


class Janus2024BulkObservablePathGateTests(unittest.TestCase):
    def test_gate_declares_non_proxy_bulk_path(self):
        payload = build_payload()
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-bulk-observable-path-gate",
        )
        self.assertFalse(payload["background_path_uses_q0_u0_proxy"])
        self.assertTrue(payload["background_path_uses_bulk_two_metric_history"])
        self.assertTrue(payload["bulk_history_built_from_cited_calibration"])
        self.assertTrue(payload["determinant_bridge_history_present"])
        self.assertTrue(payload["determinant_weighted_cross_density_present"])
        self.assertTrue(payload["present_e_plus_is_unity"])
        self.assertTrue(payload["e_plus_from_bulk_history_present"])


if __name__ == "__main__":
    unittest.main()
