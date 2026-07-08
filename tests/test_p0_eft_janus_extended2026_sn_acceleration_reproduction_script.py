import unittest

from scripts.build_p0_eft_janus_extended2026_sn_acceleration_reproduction import (
    build_payload,
)


class JanusExtended2026SnAccelerationReproductionScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_payload_shape(self):
        payload = self.payload
        self.assertEqual(payload["status"], "janus-extended2026-sn-acceleration-reproduction")
        self.assertTrue(payload["analytic_reproduction"]["exact_shape_recovered"])
        self.assertIn("dataset_available_locally", payload["paper_native_jla_reproduction"])
        self.assertIn("best_fit_q0", payload["supplementary_local_sn_dataset_diagnostic"])

    def test_jla_run_shape_when_available(self):
        jla = self.payload["paper_native_jla_reproduction"]
        if not jla["dataset_available_locally"]:
            self.assertEqual(jla["status"], "blocked_missing_jla_dataset")
            return
        self.assertTrue(jla["exact_q0_refit_on_original_dataset_run"])
        self.assertEqual(jla["n"], 740)
        self.assertIn("alpha", jla["fixed_nuisance"])


if __name__ == "__main__":
    unittest.main()
