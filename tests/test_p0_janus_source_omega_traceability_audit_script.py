from __future__ import annotations

import unittest

from scripts.build_p0_janus_source_omega_traceability_audit import build_payload, render_markdown


class P0JanusSourceOmegaTraceabilityAuditTests(unittest.TestCase):
    def test_audit_is_bounded_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-omega-traceability-open")
        self.assertEqual(payload["candidate_count"], 4)
        self.assertFalse(payload["omega_u_zero_source_law_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])
        self.assertIn("no prediction", payload["scope"])

    def test_candidate_sources_cover_requested_routes(self) -> None:
        rows = " ".join(
            row["candidate"] + " " + row["anchor"] + " " + row["available_content"]
            for row in build_payload()["candidate_sources"]
        )

        self.assertIn("M15/B_4vol", rows)
        self.assertIn("M15 Eqs. 4a-4b", rows)
        self.assertIn("pulled dust action", rows)
        self.assertIn("FW/comoving", rows)
        self.assertIn("source congruence/cross-force", rows)

    def test_traceability_statuses_and_blockers_stay_open(self) -> None:
        payload = build_payload()
        statuses = {row["traceability_status"] for row in payload["candidate_sources"]}
        blockers = " ".join(payload["blockers"] + [row["blocker"] for row in payload["candidate_sources"]])

        self.assertIn("partial-anchor", statuses)
        self.assertIn("open", statuses)
        self.assertIn("candidate-only", statuses)
        self.assertIn("route-open", statuses)
        self.assertTrue(payload["b4vol_measure_anchor_found"])
        self.assertFalse(payload["pulled_dust_action_derivation_closed"])
        self.assertFalse(payload["fw_comoving_source_selected"])
        self.assertFalse(payload["source_congruence_or_cross_force_closed"])
        self.assertFalse(payload["same_l_omega_k_qcross_closed"])
        self.assertIn("does not derive D_u L", blockers)
        self.assertIn("Omega source law", blockers)
        self.assertIn("shared L/Omega", blockers)

    def test_markdown_lists_candidates_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| candidate | anchor | available content | traceability status | blocker |", markdown)
        self.assertIn("M15/B_4vol field-source slot", markdown)
        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("none supplies a source law", markdown)


if __name__ == "__main__":
    unittest.main()
