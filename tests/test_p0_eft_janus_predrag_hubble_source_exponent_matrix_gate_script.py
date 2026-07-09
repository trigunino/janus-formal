import unittest

from janus_lab.janus_phase_space_occupation_search import (
    predrag_hubble_source_exponent_matrix_payload,
)


class JanusPredragHubbleSourceExponentMatrixGateTests(unittest.TestCase):
    def test_only_bridge_vacuum_is_shallow_enough_without_ionization(self):
        payload = predrag_hubble_source_exponent_matrix_payload()

        self.assertEqual(
            payload["viable_for_native_drag_without_ionization"],
            ["bridge_or_vacuum_state_energy"],
        )

    def test_radiation_fails_and_matter_is_boundary(self):
        payload = predrag_hubble_source_exponent_matrix_payload()
        rows = {row["name"]: row for row in payload["components"]}

        self.assertEqual(rows["radiation_fluid"]["H_exponent"], -2.0)
        self.assertEqual(rows["conserved_matter_or_baryons"]["H_exponent"], -1.5)
        self.assertEqual(rows["curvature_like_term"]["H_exponent"], -1.5)


if __name__ == "__main__":
    unittest.main()
