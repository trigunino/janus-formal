from __future__ import annotations

import unittest

import numpy as np

from janus_lab.weak_lensing_spectra import (
    arcmin_to_rad,
    convergence_power_limber,
    janus_lens_grid,
    janus_source_efficiency,
    janus_xi_curves_for_kids_bins,
    source_bin_from_nz_rows,
    xi_pm_from_pkappa,
)


class WeakLensingSpectraTests(unittest.TestCase):
    def test_zero_weyl_power_gives_zero_convergence_and_xi(self) -> None:
        ell = np.geomspace(10.0, 100.0, 8)
        z = np.linspace(0.1, 1.0, 16)
        chi = np.linspace(100.0, 1000.0, 16)
        efficiency = np.ones_like(z)

        pkappa = convergence_power_limber(
            ell,
            z,
            chi,
            efficiency,
            efficiency,
            lambda k, z_grid: np.zeros_like(k),
        )
        xi_plus, xi_minus = xi_pm_from_pkappa(arcmin_to_rad(np.asarray([1.0, 10.0])), ell, pkappa)

        self.assertTrue(np.allclose(pkappa, 0.0))
        self.assertTrue(np.allclose(xi_plus, 0.0))
        self.assertTrue(np.allclose(xi_minus, 0.0))

    def test_projection_factor_enters_limber_integrand(self) -> None:
        ell = np.asarray([10.0])
        z = np.asarray([0.1, 0.2, 0.3])
        chi = np.asarray([100.0, 200.0, 300.0])
        efficiency = np.ones_like(z)

        base = convergence_power_limber(ell, z, chi, efficiency, efficiency, lambda k, z_grid: np.ones_like(k))
        doubled = convergence_power_limber(
            ell,
            z,
            chi,
            efficiency,
            efficiency,
            lambda k, z_grid: np.ones_like(k),
            projection_factor=lambda z_lens: 2.0 * np.ones_like(z_lens),
        )

        self.assertTrue(np.allclose(doubled, 2.0 * base))

    def test_angular_lens_distance_kernel_reduces_efficiency(self) -> None:
        model, z_lens, _chi = janus_lens_grid(1.0, q0=-0.087, samples=8)
        source_z = np.asarray([0.8])
        source_weights = np.asarray([1.0])

        comoving = janus_source_efficiency(z_lens, source_z, source_weights, model, distance_kernel="comoving")
        angular = janus_source_efficiency(z_lens, source_z, source_weights, model, distance_kernel="angular_lens")

        mask = comoving > 0.0
        self.assertTrue(np.all(angular[mask] < comoving[mask]))

    def test_source_bin_uses_bin_specific_redshift_key_when_present(self) -> None:
        rows = [
            {"Z_MID": 0.1, "Z_MID_BIN2": 0.3, "BIN1": 1.0, "BIN2": 1.0},
            {"Z_MID": 0.2, "Z_MID_BIN2": 0.4, "BIN1": 1.0, "BIN2": 1.0},
        ]

        z, _weights = source_bin_from_nz_rows(rows, 2)

        self.assertTrue(np.allclose(z, [0.3, 0.4]))

    def test_janus_xi_curves_emit_all_kids_pairs(self) -> None:
        nz_rows = []
        for z in np.linspace(0.1, 1.0, 8):
            row = {"Z_MID": float(z)}
            for index in range(1, 6):
                row[f"BIN{index}"] = 1.0 if index == 1 else 0.2
            nz_rows.append(row)

        xi_plus, xi_minus = janus_xi_curves_for_kids_bins(
            nz_rows,
            np.asarray([1.0, 10.0]),
            ell=np.geomspace(10.0, 100.0, 8),
        )

        self.assertEqual(len(xi_plus), 15)
        self.assertEqual(set(xi_plus), set(xi_minus))
        self.assertEqual(xi_plus[(1, 1)].shape, (2,))


if __name__ == "__main__":
    unittest.main()
