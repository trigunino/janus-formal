import unittest

from janus_lab.janus_phase_space_occupation_search import amin_integer_sector_requirements_payload


class JanusAminIntegerSectorRequirementsGateTests(unittest.TestCase):
    def test_required_integer_is_about_drag_redshift(self):
        payload = amin_integer_sector_requirements_payload()

        self.assertEqual(payload["required_N_min"], 1001)

    def test_projective_cover_does_not_supply_large_N(self):
        payload = amin_integer_sector_requirements_payload()
        rows = {row["name"]: row for row in payload["candidates"]}

        self.assertEqual(rows["covering_degree"]["N"], 2)
        self.assertEqual(rows["covering_degree"]["status"], "fails")
        self.assertEqual(rows["large_boundary_hilbert_dimension"]["status"], "possible_but_needs_state_law")


if __name__ == "__main__":
    unittest.main()
