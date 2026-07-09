import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_exterior_power_consistency_audit_payload,
)


class JanusM31ExteriorPowerConsistencyAuditGateTests(unittest.TestCase):
    def test_additive_count_matches_but_is_not_m31_legal(self):
        payload = m31_exterior_power_consistency_audit_payload()
        additive = next(
            row for row in payload["alternatives"] if row["name"] == "additive_CPT_as_fermionic_modes"
        )

        self.assertEqual(additive["dimension"], 1001)
        self.assertTrue(additive["matches_required_N"])
        self.assertFalse(additive["structurally_legal_from_M31"])

    def test_m31_legal_readings_do_not_match_required_N(self):
        payload = m31_exterior_power_consistency_audit_payload()

        self.assertEqual(payload["legal_matches"], [])
        self.assertFalse(payload["current_no_fit_selector_survives_audit"])
        legal = [
            row for row in payload["alternatives"] if row["structurally_legal_from_M31"]
        ]
        self.assertTrue(all(not row["matches_required_N"] for row in legal))


if __name__ == "__main__":
    unittest.main()
