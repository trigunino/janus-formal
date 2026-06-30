from __future__ import annotations

import unittest

from scripts.build_bianchi_flrw_dust_transport_branch import build_payload


class BianchiFlrwDustTransportBranchTests(unittest.TestCase):
    def test_branch_closes_only_special_scalar_case(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["branch_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertIn("dust only", " ".join(payload["assumptions"]))

    def test_positive_branch_separates_determinant_from_transport(self) -> None:
        branch = build_payload()["positive_branch"]

        self.assertIn("3(H_minus-H_plus)", branch["transport_condition"])
        self.assertEqual(
            branch["combined_weight"],
            "weight3_dust_plus proportional (a_minus/a_plus)^3",
        )

    def test_negative_branch_is_symmetric(self) -> None:
        branch = build_payload()["negative_branch"]

        self.assertIn("3(H_plus-H_minus)", branch["transport_condition"])
        self.assertEqual(
            branch["combined_weight"],
            "weight3_dust_minus proportional (a_plus/a_minus)^3",
        )

    def test_non_claims_block_lensing_amplitude(self) -> None:
        non_claims = " ".join(build_payload()["non_claims"])

        self.assertIn("does not derive Q_cross", non_claims)
        self.assertIn("does not turn a_minus/a_plus into a lensing amplitude", non_claims)

    def test_notation_guards_prevent_qdet_double_count(self) -> None:
        guards = " ".join(build_payload()["notation_guards"])

        self.assertIn("(a_minus/a_plus)^4", guards)
        self.assertIn("(a_minus/a_plus)^-1", guards)
        self.assertIn("not multiply a positive-effective density by det4_metric_plus again", guards)

    def test_notation_names_metric_and_dust_layers_separately(self) -> None:
        notation = build_payload()["notation"]

        self.assertIn("det4_metric_plus", notation)
        self.assertIn("transport3_dust_plus", notation)
        self.assertIn("weight3_dust_plus", notation)


if __name__ == "__main__":
    unittest.main()
