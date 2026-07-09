import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    isotropy_preserving_anormal_ordering_obstruction_payload,
)


class JanusIsotropyPreservingANormalOrderingObstructionGateTests(unittest.TestCase):
    def test_isotropic_blocks_do_not_order_full_sym4(self):
        payload = isotropy_preserving_anormal_ordering_obstruction_payload()
        self.assertEqual(payload["full_sym4_levels"], 1001)
        self.assertEqual(payload["isotropic_block_profile_levels"], 70)
        self.assertFalse(payload["orders_1001_while_isotropic"])

    def test_escape_routes_are_explicit(self):
        payload = isotropy_preserving_anormal_ordering_obstruction_payload()
        routes = " ".join(payload["allowed_non_rustine_escape_routes"])
        self.assertIn("SO(3)-invariant", routes)
        self.assertIn("isotropic observable averaging", routes)


if __name__ == "__main__":
    unittest.main()
