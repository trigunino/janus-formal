import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    entropy_to_ruler_resolution_map_payload,
)


class JanusEntropyToRulerResolutionMapGateTests(unittest.TestCase):
    def test_entropy_map_gives_required_resolution(self):
        payload = entropy_to_ruler_resolution_map_payload()
        m = payload["mathematical_map"]
        self.assertEqual(m["N_cells"], 1001)
        self.assertTrue(m["a_min_equals_exp_minus_S"])
        self.assertAlmostEqual(m["a_min"], 1.0 / 1001.0)
        self.assertAlmostEqual(m["z_max"], 1000.0)

    def test_drag_coupling_is_not_claimed(self):
        payload = entropy_to_ruler_resolution_map_payload()
        self.assertFalse(payload["what_is_not_closed"]["photon_baryon_drag_uses_this_resolution"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
