from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_connection_difference_cancellation import (
    build_payload,
    render_markdown,
)


class P0StueckelbergConnectionDifferenceCancellationTests(unittest.TestCase):
    def test_artifact_is_conditional_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "connection-difference-cancellation-conditional-open")
        self.assertEqual(payload["branch"], "zero_parameter_stueckelberg_dust")
        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters"], [])
        self.assertTrue(payload["same_l_k_qcross_required"])
        self.assertTrue(payload["receiver_connection_geodesic_required"])
        self.assertTrue(payload["e_phi_related"])
        self.assertTrue(payload["e_l_related"])
        self.assertFalse(payload["connection_difference_terms_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_connection_terms_cover_plus_minus_and_receiver_geodesics(self) -> None:
        terms = {row["sector"]: row for row in build_payload()["connection_terms"]}

        self.assertIn("plus", terms)
        self.assertIn("minus", terms)
        self.assertEqual(terms["plus"]["connection"], "C_plus-minus")
        self.assertEqual(terms["minus"]["connection"], "C_minus-plus")
        self.assertIn("D_plus_nu u_-to+", terms["plus"]["receiver_geodesic_condition"])
        self.assertIn("D_minus_b u_+to-", terms["minus"]["receiver_geodesic_condition"])
        self.assertIn("source geodesics into plus geodesics", terms["plus"]["transport_condition"])
        self.assertIn("source geodesics into minus geodesics", terms["minus"]["transport_condition"])
        self.assertEqual(terms["plus"]["closed"], "conditional")
        self.assertEqual(terms["minus"]["closed"], "conditional")

    def test_required_identities_include_e_phi_e_l_same_l_and_d_self_u(self) -> None:
        identities = {row["name"]: row for row in build_payload()["required_identities"]}

        self.assertIn("receiver_connection_transported_geodesic", identities)
        self.assertIn("E_phi_transport_identity", identities)
        self.assertIn("E_L_transport_identity", identities)
        self.assertIn("same_L_for_K_and_Qcross", identities)
        self.assertIn("D_self u_to = 0", identities["receiver_connection_transported_geodesic"]["equation"])
        self.assertIn("E_phi", identities["E_phi_transport_identity"]["equation"])
        self.assertIn("E_L", identities["E_L_transport_identity"]["equation"])
        self.assertIn("Q_cross", identities["same_L_for_K_and_Qcross"]["equation"])
        self.assertTrue(all(row["proven_here"] is False for row in identities.values()))

    def test_cancellation_tests_are_no_fit_and_conditional(self) -> None:
        payload = build_payload()
        decision = payload["closure_decision"]

        self.assertEqual(decision["connection_difference_terms_vanish"], "conditional")
        self.assertFalse(decision["closure"])
        self.assertTrue(decision["conditional_closure_possible"])
        self.assertIn("same L", decision["open_reason"])
        self.assertTrue(all(row["fit_used"] is False for row in payload["cancellation_tests"]))
        self.assertTrue(all(row["result"] == "vanishes_conditionally" for row in payload["cancellation_tests"]))

    def test_markdown_reports_open_closure_conditions(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Fit used: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Connection-difference terms closed: False", markdown)
        self.assertIn("D_self u_to=0", markdown)
        self.assertIn("E_phi", markdown)
        self.assertIn("E_L", markdown)
        self.assertIn("same-L K/Qcross", markdown)


if __name__ == "__main__":
    unittest.main()
