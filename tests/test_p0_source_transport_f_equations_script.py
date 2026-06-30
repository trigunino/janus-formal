from __future__ import annotations

import unittest

from scripts.build_p0_source_transport_f_equations import build_payload


class P0SourceTransportFEquationsTests(unittest.TestCase):
    def test_f_constraints_are_written_but_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["f_constraints_written"])
        self.assertTrue(payload["lorentz_preservation_written"])
        self.assertTrue(payload["plus_residual_constraints_written"])
        self.assertTrue(payload["minus_residual_constraints_written"])
        self.assertFalse(payload["source_derived_f_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_lorentz_preservation_constrains_f(self) -> None:
        text = " ".join(build_payload()["lorentz_preservation"])

        self.assertIn("F_minus_to_plus^T eta L_minus_to_plus", text)
        self.assertIn("F_plus_to_minus^T eta L_plus_to_minus", text)
        self.assertIn("eta-antisymmetric", text)

    def test_plus_and_minus_constraints_include_continuity_and_force(self) -> None:
        payload = build_payload()
        plus = " ".join(row["name"] + row["equation"] + row["f_content"] for row in payload["plus_constraints"])
        minus = " ".join(row["name"] + row["equation"] + row["f_content"] for row in payload["minus_constraints"])

        self.assertIn("transported_continuity_plus", plus)
        self.assertIn("receiver_force_plus", plus)
        self.assertIn("F_minus_to_plus", plus)
        self.assertIn("transported_continuity_minus", minus)
        self.assertIn("receiver_force_minus", minus)
        self.assertIn("F_plus_to_minus", minus)

    def test_density_measure_terms_are_not_dropped(self) -> None:
        constraints = " ".join(build_payload()["density_measure_constraints"])

        self.assertIn("B_plus", constraints)
        self.assertIn("B_minus", constraints)
        self.assertIn("cannot be dropped", constraints)

    def test_closure_is_conditional_and_f_is_underdetermined(self) -> None:
        payload = build_payload()
        closure = " ".join(payload["minimal_closure_statement"])
        open_items = " ".join(payload["still_not_source_derived"])

        self.assertTrue(payload["r_plus_closed_conditionally"])
        self.assertTrue(payload["r_minus_closed_conditionally"])
        self.assertIn("then Lorentz-transported dust closes", closure)
        self.assertIn("underdetermined", open_items)
        self.assertIn("transverse/gauge", open_items)


if __name__ == "__main__":
    unittest.main()
