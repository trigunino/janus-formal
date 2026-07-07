import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_internal_constraints import (
    build_payload as internal_constraints,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_path_end_to_end_audit import (
    build_payload as e2e,
)


class SigmaDiscreteInternalAndE2ETests(unittest.TestCase):
    def test_internal_constraints_ready_on_active_inputs(self):
        payload = internal_constraints()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["internal_constraints_ready"])
        self.assertEqual(payload["surviving_sectors"], [1, 2, 3, 4, 5, 6, 7, 8])
        self.assertFalse(payload["diagnostic_rankings_are_constraints"])
        self.assertFalse(payload["internal_unique_sector_selected"])
        self.assertEqual(payload["diagnostic_rankings"]["radius_ascending"], [1, 2, 3, 4, 5, 6, 7, 8])
        self.assertEqual(payload["diagnostic_rankings"]["spectral_scale_descending"], [1, 2, 3, 4, 5, 6, 7, 8])

    def test_internal_constraints_block_observational_fit(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(
                json.dumps(
                    {
                        "constraints_declared_before_scan": True,
                        "observational_fit_used": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = internal_constraints(path)

        self.assertFalse(payload["internal_constraints_ready"])
        self.assertIn("no_observational_fit", payload["blocked_by"])

    def test_end_to_end_discrete_path_ready(self):
        payload = e2e()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["end_to_end_path_ready"])
        self.assertEqual(payload["sector_count"], 8)
        self.assertEqual(payload["scan_survivors"], [1, 2, 3, 4, 5, 6, 7, 8])


if __name__ == "__main__":
    unittest.main()
