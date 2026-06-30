from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_transport_axiom_candidate_statement import (
    build_payload,
    render_markdown,
    write_reports,
)


class P0TransportAxiomCandidateStatementTests(unittest.TestCase):
    def test_candidate_is_written_but_not_adopted_or_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "candidate-statement-only")
        self.assertTrue(payload["candidate_written"])
        self.assertFalse(payload["adopted"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["fit_used"])

    def test_axiom_statement_contains_required_transport_content(self) -> None:
        statement = " ".join(build_payload()["axiom_statement"].values())

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", statement)
        self.assertIn("Omega_u u=0", statement)
        self.assertIn("rank-one dust", statement)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", statement)
        self.assertIn("K transport", statement)
        self.assertIn("Q_cross", statement)
        self.assertIn("lensing", statement)

    def test_candidate_excludes_pressure_pi_and_fits(self) -> None:
        payload = build_payload()
        statement = " ".join(payload["axiom_statement"].values())

        self.assertTrue(payload["pressure_pi_excluded"])
        self.assertIn("Pressure", statement)
        self.assertIn("Pi", statement)
        self.assertIn("No parameter fit", statement)
        self.assertIn("post-hoc component choice", statement)

    def test_markdown_renders_boundary_flags(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Candidate written: True", markdown)
        self.assertIn("Adopted: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Pressure/Pi excluded: True", markdown)

    def test_write_reports_creates_json_and_markdown(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = write_reports(root / "candidate.md", root / "candidate.json")

            self.assertTrue((root / "candidate.md").exists())
            self.assertTrue((root / "candidate.json").exists())
            self.assertTrue(payload["candidate_written"])


if __name__ == "__main__":
    unittest.main()
