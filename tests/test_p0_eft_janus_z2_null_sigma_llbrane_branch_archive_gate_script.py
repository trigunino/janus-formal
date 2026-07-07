import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_branch_archive_gate import (
    build_payload,
)


class NullSigmaLLBraneBranchArchiveGateTests(unittest.TestCase):
    def test_archive_keeps_llbrane_as_state_parameter_extension(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["archive_decision"],
            "archive_as_viable_state_parameter_extension",
        )
        self.assertEqual(payload["strict_no_extension_status"], "blocked")
        self.assertEqual(
            payload["LL_brane_extension_status"],
            "viable_but_chi_LL_state_parameter",
        )
        self.assertEqual(payload["open_blocker"], "chi_LL_abs_inverse_m_not_derived")
        self.assertIn("do_not_claim_no_fit_prediction", payload["forbidden_claims"])


if __name__ == "__main__":
    unittest.main()
