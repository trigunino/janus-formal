import unittest

from scripts.build_p0_eft_janus_alpha_superselection_sector_program_gate import build_payload


class JanusAlphaSuperselectionSectorProgramTests(unittest.TestCase):
    def test_alpha_contract_is_sector_not_no_fit(self):
        payload = build_payload()
        contract = payload["alpha_contract"]

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(contract["alpha_is_global_state_sector"])
        self.assertFalse(contract["alpha_is_local_fit_parameter"])
        self.assertFalse(contract["full_no_fit_prediction"])

    def test_observational_endpoint_is_sn_bao_first(self):
        payload = build_payload()
        endpoint = payload["observational_endpoint"]

        self.assertFalse(endpoint["SN"]["breaks_absolute_alpha_scale"])
        self.assertTrue(endpoint["BAO"]["breaks_absolute_alpha_scale"])
        self.assertFalse(endpoint["CMB"]["allowed_now"])


if __name__ == "__main__":
    unittest.main()
