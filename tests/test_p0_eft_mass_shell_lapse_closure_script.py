from __future__ import annotations

import unittest

from scripts.build_p0_eft_mass_shell_lapse_closure import build_payload


class P0EFTMassShellLapseClosureTests(unittest.TestCase):
    def test_active_source_measure_conditionally_closed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["det_L_solder_closed_abs"])
        self.assertTrue(status["receiver_p0_lapse_factor_closed"])
        self.assertTrue(status["active_source_measure_closed_conditionally"])
        self.assertFalse(status["prediction_ready_unconditional"])


if __name__ == "__main__":
    unittest.main()
