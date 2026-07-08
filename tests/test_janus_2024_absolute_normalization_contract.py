import unittest

import numpy as np

from janus_lab.janus_2024_bulk_path import (
    Janus2024BulkObservablePath,
    absolute_normalization_contract_from_payload,
)


class Janus2024AbsoluteNormalizationContractTests(unittest.TestCase):
    def test_contract_builds_reference(self):
        contract = absolute_normalization_contract_from_payload(
            {
                "rho_plus0_abs_kg_m3": 0.1,
                "rho_minus0_abs_kg_m3": -1.9,
                "rho_minus0_over_rho_plus0": -19.0,
            },
            e_global=1.0,
            c_plus_m_s=5.0,
            c_minus_m_s=1.0,
            g_si=1.0,
        )
        reference = contract.to_reference()
        self.assertEqual(reference.k_plus, -1)
        self.assertEqual(reference.k_minus, -1)

    def test_contract_feeds_determinant_weighted_cross_density(self):
        contract = absolute_normalization_contract_from_payload(
            {
                "rho_plus0_abs_kg_m3": 0.1,
                "rho_minus0_abs_kg_m3": -1.9,
                "rho_minus0_over_rho_plus0": -19.0,
            },
            e_global=1.0,
            c_plus_m_s=5.0,
            c_minus_m_s=1.0,
            g_si=1.0,
        )
        path = Janus2024BulkObservablePath(
            x0=np.array([0.0, 1.0, 2.0], dtype=float),
            a_plus=np.array([0.5, 0.75, 1.0], dtype=float),
            adot_plus=np.array([0.2, 0.22, 0.25], dtype=float),
            a_minus=np.array([0.4, 0.6, 0.8], dtype=float),
            adot_minus=np.array([0.05, 0.06, 0.08], dtype=float),
        )
        weighted = path.determinant_weighted_cross_density(contract)
        self.assertEqual(weighted.shape, (3,))
        self.assertTrue(np.all(weighted < 0.0))


if __name__ == "__main__":
    unittest.main()
