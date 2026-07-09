import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    determinant_ratio_to_weyl_omega_obstruction_payload,
)


class JanusDeterminantRatioToWeylOmegaObstructionGateTests(unittest.TestCase):
    def test_ratio_does_not_uniquely_fix_omega(self):
        payload = determinant_ratio_to_weyl_omega_obstruction_payload()
        self.assertTrue(payload["checks"]["janus_determinant_ratio_available"])
        self.assertFalse(payload["checks"]["unique_omega_from_ratio_derived"])
        self.assertFalse(payload["closed_now"])


if __name__ == "__main__":
    unittest.main()
