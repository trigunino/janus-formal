import unittest

from janus_lab.janus_2024_reference import (
    Janus2024FLRWReference,
    Janus2024PublishedCitedObservationReference,
    Janus2024PublishedDustBackground,
    Janus2024PublishedObservationalAnchors,
    JanusPublishedExactShapeReference,
)


class Janus2024FLRWReferenceTests(unittest.TestCase):
    def test_published_background_equations_are_paper_native(self):
        model = Janus2024PublishedDustBackground()
        self.assertEqual(model.common_time_coordinate, "x0")
        self.assertEqual(model.k_plus, -1)
        self.assertEqual(model.k_minus, -1)
        self.assertEqual(
            model.conservation_law,
            ("rho_plus * c_plus^2 * a_plus^3", "rho_minus * c_minus^2 * a_minus^3"),
        )

    def test_published_observational_anchors_are_explicit(self):
        model = Janus2024PublishedObservationalAnchors()
        self.assertEqual(model.direct_standard_candle_h0_km_s_mpc, 70.0)
        self.assertEqual(model.lcdm_cmb_h0_km_s_mpc, 67.0)
        self.assertTrue(model.exact_fit_curve_claim_present)

    def test_published_exact_shape_reference_is_normalized(self):
        model = JanusPublishedExactShapeReference()
        self.assertEqual(model.q0, -0.087)
        self.assertGreater(model.u0, 0.0)
        self.assertAlmostEqual(model.normalized_a(model.u0), 1.0)
        self.assertAlmostEqual(model.normalized_e(model.u0), 1.0)
        history = model.sample_normalized_plus_history(samples=8)
        self.assertEqual(len(history["u"]), 8)
        self.assertAlmostEqual(float(history["a_plus"][-1]), 1.0)
        self.assertAlmostEqual(float(history["e_plus"][-1]), 1.0)

    def test_published_cited_observation_reference_is_materialized(self):
        model = Janus2024PublishedCitedObservationReference()
        self.assertEqual(model.q0, -0.087)
        self.assertEqual(model.h0_km_s_mpc, 70.0)
        self.assertGreater(model.u0, 0.0)
        self.assertGreater(model.alpha_seconds, 0.0)

    def test_global_energy_route_reconstructs_densities(self):
        model = Janus2024FLRWReference.from_global_energy_and_ratio(
            e_global=1.0,
            rho_minus0_over_rho_plus0=-19.0,
            c_plus_m_s=5.0,
            c_minus_m_s=1.0,
            g_si=1.0,
        )
        self.assertGreater(model.rho_plus0_kg_m3, 0.0)
        self.assertLess(model.rho_minus0_kg_m3, 0.0)
        self.assertAlmostEqual(model.conserved_energy(1.0, 1.0), 1.0)

    def test_paper_curvature_branch_is_fixed(self):
        model = Janus2024FLRWReference(
            e_global=1.0,
            rho_plus0_kg_m3=1.0,
            rho_minus0_kg_m3=-1.0,
            c_plus_m_s=1.0,
            c_minus_m_s=1.0,
            g_si=1.0,
        )
        self.assertEqual(model.k_plus, -1)
        self.assertEqual(model.k_minus, -1)

    def test_rhs_has_opposite_sector_acceleration_signs(self):
        model = Janus2024FLRWReference(
            e_global=2.0,
            rho_plus0_kg_m3=1.0,
            rho_minus0_kg_m3=-1.0,
            c_plus_m_s=1.0,
            c_minus_m_s=1.0,
            g_si=1.0,
        )
        rhs = model.rhs(0.0, (2.0, 3.0, 4.0, 5.0))
        self.assertEqual(rhs[0], 3.0)
        self.assertEqual(rhs[2], 5.0)
        self.assertLess(rhs[1], 0.0)
        self.assertGreater(rhs[3], 0.0)


if __name__ == "__main__":
    unittest.main()
