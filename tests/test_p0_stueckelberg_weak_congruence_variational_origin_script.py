from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_weak_congruence_variational_origin import build_payload


class P0WeakCongruenceVariationalOriginTests(unittest.TestCase):
    def test_variational_shape_exists_but_is_not_closure(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["minimal_variational_shape_found"])
        self.assertFalse(decision["source_derived"])
        self.assertFalse(decision["accepted_as_final_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_multiplier_must_not_be_new_free_field(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["rejection_rules"])
        accepted = " ".join(payload["accepted_without_new_axiom"])

        self.assertIn("independent lambda_plus/lambda_minus", rules)
        self.assertIn("existing dust current", accepted)
        self.assertTrue(payload["decision"]["requires_new_multiplier_if_not_from_matter_variation"])

    def test_candidate_targets_both_mirror_residuals(self) -> None:
        payload = build_payload()
        targets = " ".join(row["target"] for row in payload["candidate_terms"])

        self.assertIn("C_plus-minus", targets)
        self.assertIn("C_minus-plus", targets)


if __name__ == "__main__":
    unittest.main()
