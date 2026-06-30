from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.run_pm_qcross_lensing_pipeline import build_payload


class PMQCrossLensingPipelineScriptTests(unittest.TestCase):
    def test_pipeline_completes_small_vectorized_run(self) -> None:
        payload = build_payload(
            Namespace(
                grid=4,
                steps=3,
                dt=0.0001,
                gravity_scale=0.5,
                box_size_mpc=1000.0,
                h0=70.0,
                time_unit_gyr=1000.0,
            )
        )

        self.assertTrue(payload["finite"])
        self.assertEqual(payload["steps_completed"], 3)
        self.assertGreater(payload["rows"][-1]["source_rms"], 0.0)
        self.assertGreaterEqual(payload["rows"][-1]["qcross_min"], 0.0)


if __name__ == "__main__":
    unittest.main()
