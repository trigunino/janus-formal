from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_camb_janus_table_wrapper import build_payload


class P0EFTCMBCAMBJanusTableWrapperTests(unittest.TestCase):
    def test_wrapper_consumes_janus_tables(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(payload["backend_solver_run"])
        self.assertTrue(payload["janus_modified_gravity_tables_consumed"])
        self.assertTrue(payload["post_camb_weyl_lensing_wrapper"])
        self.assertFalse(payload["exact_camb_fork"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])

    def test_wrapped_cls_csv_exists(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(Path(payload["wrapper"]["wrapped_cls_csv"]).exists())
        self.assertGreaterEqual(payload["wrapper"]["max_abs_fractional_shift"], 0.0)


if __name__ == "__main__":
    unittest.main()
