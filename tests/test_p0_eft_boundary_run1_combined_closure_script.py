from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_run1_combined_closure import build_payload, render_markdown


class P0EFTBoundaryRun1CombinedClosureTests(unittest.TestCase):
    def test_run1_is_algebraically_closed_not_geometric(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["lambda_geometrically_closed"])
        self.assertTrue(status["run1_algebraically_closed"])
        self.assertFalse(status["kappa_geometrically_derived"])
        self.assertFalse(status["beta_geometrically_derived"])
        self.assertFalse(status["run1_pure_geometric_closure"])
        self.assertFalse(status["prediction_ready"])

    def test_resulting_coefficients_satisfy_factorization(self) -> None:
        result = build_payload()["combined"]["resulting_coefficients"]

        self.assertEqual(result["m_I"], "0")
        self.assertEqual(result["m_C"], "0")
        self.assertEqual(result["m_G"], "sigma*eps_n*m_N")

    def test_obligations_are_kappa_beta_only(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("derive kappa", obligations)
        self.assertIn("derive beta", obligations)
        self.assertNotIn("derive lambda", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("run1_algebraically_closed: True", markdown)
        self.assertIn("run1_pure_geometric_closure: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
