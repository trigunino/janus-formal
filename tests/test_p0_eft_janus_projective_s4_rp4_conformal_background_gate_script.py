import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    projective_s4_rp4_conformal_background_payload,
)


class JanusProjectiveS4RP4ConformalBackgroundGateTests(unittest.TestCase):
    def test_projective_geometry_closes_hat_not_cosmology(self):
        payload = projective_s4_rp4_conformal_background_payload()
        self.assertTrue(payload["hat_background_geometry_closed"])
        self.assertFalse(payload["predictive_cosmology_closed"])
        self.assertIn("Omega_S4", payload["geometry"]["omega_s4"])


if __name__ == "__main__":
    unittest.main()
