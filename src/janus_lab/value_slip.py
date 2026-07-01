"""Value-slip scaffolding for Janus-Holst lensing.

This module deliberately encodes only the non-fit interface.  It does not
derive the Green kernel and refuses residual-derived shortcuts.
"""

from __future__ import annotations

from collections.abc import Callable

import numpy as np


Array = np.ndarray
KernelFunction = Callable[[Array, Array], Array]

_FORBIDDEN_PROVENANCE = {
    "kids_residual",
    "kids_pair23",
    "kids_delta_z",
    "photoz_fit",
    "bin_factor_fit",
    "amplitude_fit",
    "eta_scan_fit",
    "tilt_scan_fit",
}

_ALLOWED_PROVENANCE = {
    "source_derived_green_kernel",
    "symbolic_scaffold",
}


def validate_value_slip_provenance(provenance: str) -> str:
    normalized = provenance.strip().lower()
    if normalized in _FORBIDDEN_PROVENANCE:
        raise ValueError("value-slip kernel cannot use KiDS residual-derived provenance.")
    if normalized not in _ALLOWED_PROVENANCE:
        raise ValueError("unknown value-slip provenance.")
    return normalized


def derivative_slip_source_shape(k: Array, a: Array, omega_t: Array, chi_x: Array) -> Array:
    k_values = np.asarray(k, dtype=float)
    a_values = np.asarray(a, dtype=float)
    omega = np.asarray(omega_t, dtype=float)
    chi = np.asarray(chi_x, dtype=float)
    if np.any(k_values < 0.0) or np.any(a_values <= 0.0):
        raise ValueError("k must be non-negative and a must be positive.")
    try:
        return omega * (1.0 - chi) * k_values * k_values / (k_values * k_values + 1.0)
    except ValueError as exc:
        raise ValueError("derivative slip inputs must broadcast.") from exc


def value_slip_from_green_kernel(
    derivative_source: Array,
    k: Array,
    a: Array,
    green_kernel: KernelFunction,
    *,
    green_kernel_computed: bool,
    provenance: str,
) -> Array:
    validate_value_slip_provenance(provenance)
    if not green_kernel_computed:
        raise ValueError("value-slip Green kernel is not computed.")
    source = np.asarray(derivative_source, dtype=float)
    kernel = np.asarray(green_kernel(np.asarray(k, dtype=float), np.asarray(a, dtype=float)), dtype=float)
    if not np.isfinite(source).all() or not np.isfinite(kernel).all():
        raise ValueError("value-slip inputs must be finite.")
    try:
        return kernel * source
    except ValueError as exc:
        raise ValueError("green kernel and derivative source must broadcast.") from exc


def sigma_from_mu_and_eta_slip(mu: Array, eta_slip: Array) -> Array:
    mu_values = np.asarray(mu, dtype=float)
    eta_values = np.asarray(eta_slip, dtype=float)
    try:
        return mu_values * (1.0 + eta_values) / 2.0
    except ValueError as exc:
        raise ValueError("mu and eta_slip must broadcast.") from exc


def scaffold_status(*, green_kernel_computed: bool, provenance: str) -> dict:
    normalized = validate_value_slip_provenance(provenance)
    return {
        "status": "value-slip-scaffold-ready" if green_kernel_computed else "value-slip-scaffold-open",
        "green_kernel_computed": bool(green_kernel_computed),
        "provenance": normalized,
        "prediction_ready": bool(green_kernel_computed and normalized == "source_derived_green_kernel"),
    }
