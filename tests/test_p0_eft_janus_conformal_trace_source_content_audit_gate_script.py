import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    conformal_trace_source_content_audit_payload,
)


class JanusConformalTraceSourceContentAuditGateTests(unittest.TestCase):
    def test_trace_recommends_00_for_predrag(self):
        payload = conformal_trace_source_content_audit_payload()
        self.assertFalse(payload["trace_is_sufficient_for_predrag"])
        self.assertEqual(payload["recommended_projection"], "ConformalEinstein00")


if __name__ == "__main__":
    unittest.main()
