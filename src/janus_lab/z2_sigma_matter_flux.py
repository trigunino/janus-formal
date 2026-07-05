"""Matter-flux component builders for the active Z2/Sigma BAO path."""

from __future__ import annotations

from collections.abc import Callable

import numpy as np

from .z2_sigma_flrw_component_manifest import FORBIDDEN_PROVENANCE_TOKENS


ArrayFn = Callable[[np.ndarray], np.ndarray]


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def make_transparent_matter_flux_components(
    *,
    active_sigma_transparency_derived: bool,
) -> tuple[ArrayFn, ArrayFn]:
    """Return zero matter-flux rho/p only after active transparency is derived."""

    if not active_sigma_transparency_derived:
        raise ValueError("active Sigma transparency must be derived before setting matter_flux=0")

    def zero(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        return np.zeros_like(grid)

    return zero, zero


def build_transparent_matter_flux_component_payload(
    *,
    a_grid: list[float] | np.ndarray,
    active_sigma_transparency_derived: bool,
    transparency_provenance: str,
) -> dict:
    """Build matter-flux component arrays only from an active transparency proof."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    provenance = _clean_source(transparency_provenance, "matter_flux_transparency")
    rho, pressure = make_transparent_matter_flux_components(
        active_sigma_transparency_derived=active_sigma_transparency_derived
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "component_route": "transparent_sigma_zero_flux",
        "active_sigma_transparency_derived": True,
        "a_grid": grid.tolist(),
        "flrw_components_over_rho_crit0": {
            "matter_flux_rho": rho(grid).tolist(),
            "matter_flux_p": pressure(grid).tolist(),
        },
        "component_provenance": {
            "matter_flux_rho": provenance,
            "matter_flux_p": provenance,
        },
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
    }
