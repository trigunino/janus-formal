import unittest

from scripts.build_p0_eft_janus_native_bao_ruler_contract_gate import build_payload


class JanusNativeBAORulerContractTests(unittest.TestCase):
    def test_contract_is_formulated_but_not_evaluable(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["native_bao_contract_formulated"])
        self.assertFalse(payload["native_bao_contract_evaluable"])
        self.assertTrue(payload["current_proxy_rejected"])

    def test_published_q0_does_not_reach_high_drag_marker(self):
        audit = build_payload()["redshift_domain_audit"]

        self.assertFalse(audit["published_q0_reaches_marker"])
        self.assertTrue(audit["sn_bao_selected_reaches_marker"])
        self.assertLess(audit["published_q0_zmax"], audit["fiducial_drag_redshift_marker"])


if __name__ == "__main__":
    unittest.main()
