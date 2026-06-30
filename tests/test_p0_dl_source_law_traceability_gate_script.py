from __future__ import annotations

import unittest

from scripts.build_p0_dl_source_law_traceability_gate import build_payload


class P0DLSourceLawTraceabilityGateTests(unittest.TestCase):
    def test_traceability_gate_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dl-source-law-traceability-open")
        self.assertTrue(payload["f_equation_constraints_written"])
        self.assertFalse(payload["source_derived_dl_law_found"])
        self.assertFalse(payload["all_trace_rows_source_derived"])
        self.assertFalse(payload["prediction_ready"])

    def test_trace_rows_cover_dl_obligations(self) -> None:
        rows = {row["row"] for row in build_payload()["trace_rows"]}

        self.assertIn("lorentz_generator", rows)
        self.assertIn("mirror_inverse_transport", rows)
        self.assertIn("transported_continuity_force", rows)
        self.assertIn("density_measure_terms", rows)
        self.assertIn("same_l_k_qcross", rows)

    def test_no_trace_row_is_source_derived(self) -> None:
        self.assertTrue(all(not row["source_derived"] for row in build_payload()["trace_rows"]))


if __name__ == "__main__":
    unittest.main()
