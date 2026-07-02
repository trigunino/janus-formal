import unittest

from scripts.build_p0_eft_janus_z4_standalone_teee_gr_reference_handshake import build_payload


class P0EFTJanusZ4StandaloneTEEEGRReferenceHandshakeTests(unittest.TestCase):
    def test_gr_reference_handshake_schema_without_running_cobaya(self):
        payload = build_payload(run=False)

        self.assertEqual(payload["status"], "janus-z4-standalone-teee-gr-reference-handshake")
        self.assertEqual(payload["mode"], "GR/CAMB reference only; frozen Z4 candidate not evaluated")
        self.assertFalse(payload["standalone_teee_gr_reference_handshake_passed"])
        self.assertFalse(payload["high_l_decomposition_trial_allowed_after_this_report"])
        self.assertEqual(payload["components"], [])


if __name__ == "__main__":
    unittest.main()
