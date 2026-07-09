import unittest

from janus_lab.janus_phase_space_occupation_search import (
    boundary_dimension_to_amin_map_audit_payload,
)


class JanusBoundaryDimensionToAminMapAuditGateTests(unittest.TestCase):
    def test_only_linear_map_reaches_predrag_for_N1001(self):
        payload = boundary_dimension_to_amin_map_audit_payload()

        self.assertEqual(payload["N"], 1001)
        self.assertEqual(payload["successful_maps"], ["linear_resolution_length"])
        self.assertTrue(payload["unique_success_is_linear_resolution"])
        self.assertFalse(payload["current_map_derived"])

    def test_area_volume_entropy_fail_predrag(self):
        payload = boundary_dimension_to_amin_map_audit_payload()
        failing = {
            row["name"]: row
            for row in payload["maps"]
            if row["name"] in {"area_resolution", "volume_resolution", "entropy_dimension"}
        }

        self.assertTrue(all(not row["matches_predrag"] for row in failing.values()))


if __name__ == "__main__":
    unittest.main()
