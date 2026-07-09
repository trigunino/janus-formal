import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    active_normal_connection_primitives_availability_payload,
)


class JanusActiveNormalConnectionPrimitivesAvailabilityGateTests(unittest.TestCase):
    def test_current_assets_do_not_materialize_active_omega(self):
        payload = active_normal_connection_primitives_availability_payload()
        self.assertFalse(payload["required_manifest_present"])
        self.assertFalse(payload["can_materialize_active_omega_perp_now"])
        self.assertFalse(payload["safe_to_create_zero_manifest_as_proof"])

    def test_required_collar_primitives_are_explicit(self):
        payload = active_normal_connection_primitives_availability_payload()
        required = " ".join(payload["next_required"])
        self.assertIn("active collar embedding", required)
        self.assertIn("partial_u N_A", required)
        self.assertIn("ambient connection", required)


if __name__ == "__main__":
    unittest.main()
