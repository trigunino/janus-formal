from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_pt67_gluing_orientation_gate import build_payload


class Z2PT67GluingOrientationGateScriptTests(unittest.TestCase):
    def test_script_reports_pt_transport_raccord(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["PT_transport_rule"]["time_covector"], "dt -> -dt")
        self.assertEqual(payload["PT_transport_rule"]["radial_covector"], "dr -> dr")
        self.assertTrue(payload["raccord_to_regular_sigma_pipeline"]["Cartan_GHY_jump_ready_under_PT_transport"])


if __name__ == "__main__":
    unittest.main()
