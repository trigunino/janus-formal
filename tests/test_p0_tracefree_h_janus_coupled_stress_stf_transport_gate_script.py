from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_janus_coupled_stress_stf_transport_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHJanusCoupledStressSTFTransportGateTests(unittest.TestCase):
    def test_gate_closes_algebra_but_not_physics(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "janus-coupled-stress-stf-transport-algebra-closed-source-open",
        )
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertTrue(payload["algebraic_transport_closed"])
        self.assertTrue(payload["same_l_bridge_stack_algebra_closed"])
        self.assertFalse(payload["same_l_bridge_stack_source_selected"])
        self.assertTrue(payload["same_l_induces_m"])
        self.assertTrue(payload["same_l_induces_k"])
        self.assertTrue(payload["same_l_induces_qcross"])
        self.assertTrue(payload["same_l_induces_vlasov_moments"])
        self.assertTrue(payload["stf_rank2_coherent"])
        self.assertEqual(payload["rank_4d_symmetric"], 10)
        self.assertEqual(payload["rank_4d_stf"], 9)
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(payload["same_bridge_source_selected"])
        self.assertFalse(payload["transport_acceptance_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_transport_definitions_include_bridge_stress_sources_and_stf(self) -> None:
        rows = {row["name"]: row for row in build_payload()["transport_definitions"]}

        self.assertIn("M_{o->s}", rows["bridge_map"]["formula"])
        self.assertIn("L_{o->s}", rows["bridge_map"]["formula"])
        self.assertIn("T_{o->s}^{mu nu}", rows["transported_stress"]["formula"])
        self.assertIn("S_+^{mu nu}=T_+^{mu nu}+B_+ T_{-->+}^{mu nu}", rows["coupled_source_plus"]["formula"])
        self.assertIn("S_-^{mu nu}=B_- T_{+->-}^{mu nu}+T_-^{mu nu}", rows["coupled_source_minus"]["formula"])
        self.assertIn("P_STF^s(S_s)", rows["tracefree_projection"]["formula"])

    def test_algebraic_results_block_scalar_absorption(self) -> None:
        rows = {row["claim"]: row for row in build_payload()["algebraic_results"]}

        self.assertTrue(rows["rank2_transport"]["closed"])
        self.assertTrue(rows["symmetry_preserved"]["closed"])
        self.assertTrue(rows["stf_type"]["closed"])
        self.assertTrue(rows["rank_count"]["closed"])
        self.assertTrue(rows["scalar_absorption_blocked"]["closed"])
        self.assertIn("B4vol is only a scalar multiplier", rows["scalar_absorption_blocked"]["result"])

    def test_open_requirements_keep_same_bridge_and_residuals(self) -> None:
        text = " ".join(build_payload()["open_requirements"])

        self.assertIn("same admissible L", text)
        self.assertIn("algebraically induces M", text)
        self.assertIn("mirror/inverse branch", text)
        self.assertIn("B4vol/J/lapse", text)
        self.assertIn("delta M", text)
        self.assertIn("R_plus=0 and R_minus=0", text)

    def test_markdown_reports_status_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Janus Coupled-Stress STF Transport", markdown)
        self.assertIn("Algebraic transport closed: True", markdown)
        self.assertIn("Same-L bridge stack algebra closed: True", markdown)
        self.assertIn("Same-L bridge stack source selected: False", markdown)
        self.assertIn("STF rank-2 coherent: True", markdown)
        self.assertIn("Scalar absorption allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
