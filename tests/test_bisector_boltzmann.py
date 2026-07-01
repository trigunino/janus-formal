from __future__ import annotations

import unittest
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.bi_sector_boltzmann import (
    acoustic_ell_proxy,
    BiSectorParams,
    BiSectorState,
    attach_conformal_distance,
    attach_photon_baryon_history,
    attach_reionization_visibility,
    apply_membrane_junction,
    attach_visibility,
    calibrate_projection_scale_from_theta_star,
    bianchi_closure_accelerations,
    calibrate_visibility_to_astar,
    cl_tt_proxy,
    continuity_residual,
    information_loss_metric,
    integrate_photon_baryon_hierarchy,
    integrate_bisector,
    line_of_sight_cl_tt_proxy,
    line_of_sight_multipole_cl_tt_proxy,
    line_of_sight_multipole_spectra_proxy,
    line_of_sight_multipole_source,
    line_of_sight_source_decomposition,
    line_of_sight_temperature_source,
    lensed_multipole_spectra_proxy,
    mode_couplings,
    mono_metric_collapsed_potential,
    metric_constraint_residual,
    metric_perturbations,
    membrane_density_jump_residual,
    newtonian_gauge_residual,
    momentum_exchange_residual,
    optical_depth_profile,
    observable_photon_potential,
    poisson_constraint_residual,
    sector_potentials,
    slip_potential,
    sound_horizon_proxy,
    theta_star_proxy,
    tt_peak_shift_proxy,
    visibility_proxy,
    visibility_from_optical_depth,
    weyl_potential,
    weyl_lensing_proxy,
    Z4ProjectionOperator,
    z4_projection_operator_diagnostics,
    z4_projection_residual,
    z4_projected_sources,
)


class BiSectorBoltzmannTests(unittest.TestCase):
    def test_zero_coupling_limit_matches_single_visible_sector(self) -> None:
        params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.0)
        state = BiSectorState(delta_plus=1.2, theta_plus=0.0, delta_minus=3.0, theta_minus=0.0)

        phi_plus, phi_minus = sector_potentials(state, params)

        self.assertAlmostEqual(phi_plus, mono_metric_collapsed_potential(state, params))
        self.assertAlmostEqual(phi_minus, 0.0)
        self.assertAlmostEqual(observable_photon_potential(state, params), phi_plus)
        self.assertLess(poisson_constraint_residual(state, params), 1e-14)
        metric = metric_perturbations(state, params)
        self.assertAlmostEqual(metric.phi_visible, phi_plus)
        self.assertLess(metric_constraint_residual(state, params), 1e-14)
        self.assertLess(newtonian_gauge_residual(state, params), 1e-14)
        self.assertLess(z4_projection_residual(state, params), 1e-14)
        self.assertEqual(len(z4_projected_sources(state, params)), 2)
        operator = Z4ProjectionOperator(params.cross_coupling)
        self.assertTrue(operator.normalized())
        self.assertAlmostEqual(operator.trace(), 2.0)
        self.assertTrue(z4_projection_operator_diagnostics(params)["normalized"])

    def test_bisector_projection_can_differ_from_monommetric_collapse(self) -> None:
        params = BiSectorParams(
            k=0.2,
            omega_plus=0.3,
            omega_minus=0.2,
            cross_coupling=0.7,
            projection_minus_weight=0.5,
        )
        state = BiSectorState(delta_plus=1.0, theta_plus=0.0, delta_minus=0.8, theta_minus=0.0)
        row = {
            "phi_obs": observable_photon_potential(state, params),
            "phi_mono": mono_metric_collapsed_potential(state, params),
        }

        self.assertGreater(information_loss_metric(row), 1e-6)

    def test_symmetric_and_antisymmetric_modes_split_when_cross_coupled(self) -> None:
        symmetric, antisymmetric = mode_couplings(BiSectorParams(cross_coupling=0.65))

        self.assertAlmostEqual(symmetric, 0.35)
        self.assertAlmostEqual(antisymmetric, 1.65)

    def test_membrane_junction_keeps_densities_continuous(self) -> None:
        params = BiSectorParams(membrane_velocity_kick=0.25)
        state = BiSectorState(delta_plus=1.0, theta_plus=0.1, delta_minus=0.8, theta_minus=-0.2)

        jumped = apply_membrane_junction(state, params)

        self.assertEqual(jumped.delta_plus, state.delta_plus)
        self.assertEqual(jumped.delta_minus, state.delta_minus)
        self.assertAlmostEqual(jumped.theta_plus, 0.35)
        self.assertAlmostEqual(jumped.theta_minus, -0.45)
        self.assertAlmostEqual(membrane_density_jump_residual(state, jumped), 0.0)

    def test_integration_is_finite(self) -> None:
        params = BiSectorParams(
            k=0.3,
            omega_plus=0.3,
            omega_minus=0.1,
            cross_coupling=0.5,
            projection_minus_weight=0.2,
            membrane_velocity_kick=0.01,
        )
        rows = integrate_bisector(
            BiSectorState(delta_plus=1e-4, theta_plus=0.0, delta_minus=5e-5, theta_minus=0.0),
            params,
            x_initial=-2.0,
            x_final=0.0,
            steps=32,
        )

        values = [value for row in rows for value in row.values()]
        self.assertTrue(np.isfinite(values).all())
        self.assertEqual(len(rows), 33)
        self.assertLess(max(abs(row["constraint_residual"]) for row in rows), 1e-12)
        self.assertLess(max(abs(row["metric_constraint_residual"]) for row in rows), 1e-12)
        self.assertLess(max(abs(row["z4_projection_residual"]) for row in rows), 1e-12)
        self.assertLess(max(abs(row["newtonian_gauge_residual"]) for row in rows), 1e-12)
        self.assertLess(max(abs(row["membrane_density_jump_residual"]) for row in rows), 1e-12)
        self.assertIn("psi_plus", rows[0])
        self.assertIn("psi_minus", rows[0])

    def test_first_observable_proxies_are_finite_positive(self) -> None:
        params = BiSectorParams(
            k=0.2,
            omega_plus=0.3,
            omega_minus=0.1,
            background_minus_weight=0.2,
            cross_coupling=0.5,
            projection_minus_weight=0.25,
        )
        rows = integrate_bisector(
            BiSectorState(delta_plus=1e-4, theta_plus=0.0, delta_minus=6e-5, theta_minus=0.0),
            params,
            x_initial=-2.0,
            x_final=0.0,
            steps=32,
        )

        self.assertGreater(sound_horizon_proxy(params), 0.0)
        self.assertGreater(theta_star_proxy(params), 0.0)
        self.assertGreater(acoustic_ell_proxy(params), 0.0)
        self.assertTrue(np.isfinite(tt_peak_shift_proxy(params)))
        self.assertGreaterEqual(weyl_lensing_proxy(rows), 0.0)
        transfer = integrate_photon_baryon_hierarchy(rows, k=params.k)
        self.assertTrue(np.isfinite(list(transfer.values())).all())
        self.assertIn("theta2_final", transfer)
        self.assertIn("neutrino_quadrupole_proxy", transfer)
        conformal_rows = attach_conformal_distance(rows, params)
        history_rows = attach_photon_baryon_history(conformal_rows, k=params.k)
        self.assertEqual(len(history_rows), len(rows))
        self.assertIn("theta0_pb", history_rows[0])
        cl_rows = cl_tt_proxy(history_rows, transfer)
        self.assertEqual(len(cl_rows), 8)
        self.assertGreater(cl_rows[0]["cl_tt_proxy"], 0.0)
        self.assertGreater(visibility_proxy(1.0 / 1090.0), visibility_proxy(0.01))
        los_source = line_of_sight_temperature_source(history_rows, transfer)
        los_rows = line_of_sight_cl_tt_proxy(history_rows, transfer)
        self.assertTrue(np.isfinite(los_source))
        self.assertEqual(len(los_rows), 8)
        visible_rows = attach_visibility(history_rows, params)
        reionized_rows = attach_reionization_visibility(visible_rows)
        self.assertIn("visibility_with_reio", reionized_rows[0])
        self.assertGreater(max(row["visibility_with_reio"] for row in reionized_rows), 0.0)
        projection_calibration = calibrate_projection_scale_from_theta_star(visible_rows, params)
        self.assertGreater(projection_calibration["projection_distance_scale"], 0.0)
        physical_los = line_of_sight_temperature_source(visible_rows, transfer)
        self.assertTrue(np.isfinite(physical_los))
        self.assertGreater(conformal_rows[0]["chi_conformal"], conformal_rows[-1]["chi_conformal"])
        self.assertLess(conformal_rows[0]["eta_conformal"], conformal_rows[-1]["eta_conformal"])
        decomposition = line_of_sight_source_decomposition(visible_rows, transfer)
        self.assertTrue(np.isfinite(list(decomposition.values())).all())
        self.assertAlmostEqual(decomposition["current_total"], physical_los)
        multipole = line_of_sight_multipole_source(
            visible_rows,
            transfer,
            k=params.k,
            ell=30,
            projection_distance_scale=projection_calibration["projection_distance_scale"],
        )
        self.assertTrue(np.isfinite(list(multipole.values())).all())
        multipole_cls = line_of_sight_multipole_cl_tt_proxy(visible_rows, transfer, k=params.k)
        self.assertEqual(len(multipole_cls), 8)
        self.assertIn("cl_tt_multipole_los_proxy", multipole_cls[0])
        spectra = line_of_sight_multipole_spectra_proxy(visible_rows, transfer, k=params.k)
        self.assertEqual(len(spectra), 8)
        self.assertIn("cl_te_proxy", spectra[0])
        self.assertIn("cl_ee_proxy", spectra[0])
        lensed = lensed_multipole_spectra_proxy(spectra, visible_rows)
        self.assertEqual(len(lensed), 8)
        self.assertIn("cl_tt_lensed_proxy", lensed[0])

    def test_optical_depth_visibility_is_normalized(self) -> None:
        params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.1, background_minus_weight=0.2)
        rows = integrate_bisector(
            BiSectorState(delta_plus=1e-4, theta_plus=0.0, delta_minus=6e-5, theta_minus=0.0),
            params,
            x_initial=-8.0,
            x_final=0.0,
            steps=128,
        )
        tau = optical_depth_profile(rows, params)
        visibility = visibility_from_optical_depth(rows, params)

        self.assertGreater(tau[0], tau[-1])
        self.assertGreater(max(visibility), 0.0)
        calibration = calibrate_visibility_to_astar(rows, params)
        self.assertLess(calibration["abs_peak_residual"], 5.0e-4)

    def test_neutrino_slip_changes_weyl_potential(self) -> None:
        params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.1, projection_minus_weight=0.25)
        state = BiSectorState(delta_plus=1e-4, theta_plus=0.0, delta_minus=6e-5, theta_minus=0.0, pi_nu=2e-5)

        self.assertGreater(slip_potential(state, params), 0.0)
        self.assertNotEqual(weyl_potential(state, params), 0.0)

    def test_continuity_residuals_are_zero_by_construction(self) -> None:
        params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.1, cross_coupling=0.5)
        state = BiSectorState(delta_plus=1e-4, theta_plus=2e-5, delta_minus=7e-5, theta_minus=-1e-5)

        plus, minus = continuity_residual(0.0, state, params)

        self.assertAlmostEqual(plus, 0.0)
        self.assertAlmostEqual(minus, 0.0)
        self.assertTrue(np.isfinite(momentum_exchange_residual(0.0, state, params)))

    def test_bianchi_closure_cancels_weighted_momentum_residual(self) -> None:
        open_params = BiSectorParams(k=0.2, omega_plus=0.3, omega_minus=0.1, cross_coupling=0.5)
        closed_params = BiSectorParams(
            k=0.2,
            omega_plus=0.3,
            omega_minus=0.1,
            cross_coupling=0.5,
            enforce_bianchi_closure=True,
        )
        state = BiSectorState(delta_plus=1e-4, theta_plus=2e-5, delta_minus=7e-5, theta_minus=-1e-5)

        closure_plus, closure_minus = bianchi_closure_accelerations(state, open_params)

        self.assertTrue(np.isfinite([closure_plus, closure_minus]).all())
        self.assertGreater(abs(momentum_exchange_residual(0.0, state, open_params)), 0.0)
        self.assertAlmostEqual(momentum_exchange_residual(0.0, state, closed_params), 0.0)


if __name__ == "__main__":
    unittest.main()
