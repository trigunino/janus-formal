from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.build_janus_ic_source_targets import build_payload


class JanusICSourceTargetsScriptTests(unittest.TestCase):
    def test_payload_separates_keeper_time_from_missing_ic_targets(self) -> None:
        payload = build_payload(
            Namespace(h0=70.0, box_size_mpc=1000.0, omega_abs=0.315, grid=8)
        )

        keepers = {item["item"]: item for item in payload["keeper_calibrations"]}
        targets = {item["target"]: item for item in payload["missing_source_targets"]}

        self.assertEqual(keepers["PM time unit"]["value"], "H0^-1")
        self.assertAlmostEqual(keepers["PM velocity unit"]["numeric_value"], 70000.0)
        self.assertEqual(set(targets), {"transfer", "growth", "amplitude", "velocity"})
        self.assertTrue(all(item["blocks_final_ic"] for item in targets.values()))
        self.assertTrue(
            all(
                item["status"] == "missing_source_derivation"
                for item in targets.values()
            )
        )
        self.assertFalse(payload["artificial_fits_allowed"])


if __name__ == "__main__":
    unittest.main()
