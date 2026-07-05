"""Active Z2/Sigma R_Sigma equation residual assembly."""

from __future__ import annotations

import numpy as np

from .z2_sigma_rsigma_certificate import validate_active_z2sigma_rsigma_solution_certificate


FORBIDDEN_RSIGMA_TERM_PROVENANCE_TOKENS = [
    "planck",
    "lcdm",
    "z4",
    "fit",
    "bao_scan",
]

EFFECTIVE_RSIGMA_EQUATION = (
    "E_RSigma(a) := E_CartanGHY(a) + E_HolstNiehYan(a) "
    "+ E_matterFlux(a) + E_counterterm(a) = 0"
)


def _checked_grid(values, name: str) -> np.ndarray:
    grid = np.asarray(values, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError(f"{name} must be one-dimensional with at least two points")
    if not np.all(np.isfinite(grid)):
        raise ValueError(f"{name} must be finite")
    return grid


def _checked_series(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    series = np.asarray(values, dtype=float)
    if series.shape != shape:
        raise ValueError(f"{name} must match a_grid shape")
    if not np.all(np.isfinite(series)):
        raise ValueError(f"{name} must be finite")
    return series


def _clean_term_provenance(value: str, name: str) -> str:
    provenance = str(value).strip()
    if not provenance:
        raise ValueError(f"{name} provenance must be nonempty")
    lowered = provenance.lower()
    if any(token in lowered for token in FORBIDDEN_RSIGMA_TERM_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {name}: {provenance}")
    return provenance


def assemble_rsigma_residual_payload(
    *,
    a_grid,
    E_CartanGHY,
    E_HolstNiehYan,
    E_matterFlux,
    E_counterterm,
    term_provenance: dict | None = None,
) -> dict:
    """Return E_RSigma(a) residual arrays from the four active radial blocks."""

    grid = _checked_grid(a_grid, "a_grid")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = grid.shape
    cartan = _checked_series(E_CartanGHY, shape, "E_CartanGHY")
    holst = _checked_series(E_HolstNiehYan, shape, "E_HolstNiehYan")
    matter = _checked_series(E_matterFlux, shape, "E_matterFlux")
    counterterm = _checked_series(E_counterterm, shape, "E_counterterm")
    provenance = term_provenance or {}
    cleaned_provenance = {
        "E_CartanGHY": _clean_term_provenance(
            provenance.get("E_CartanGHY", "active_Cartan_GHY_radial_block"),
            "E_CartanGHY",
        ),
        "E_HolstNiehYan": _clean_term_provenance(
            provenance.get("E_HolstNiehYan", "active_Holst_Nieh_Yan_radial_block"),
            "E_HolstNiehYan",
        ),
        "E_matterFlux": _clean_term_provenance(
            provenance.get("E_matterFlux", "active_matter_flux_radial_block"),
            "E_matterFlux",
        ),
        "E_counterterm": _clean_term_provenance(
            provenance.get("E_counterterm", "active_counterterm_radial_block"),
            "E_counterterm",
        ),
    }
    residual = cartan + holst + matter + counterterm
    return {
        "effective_RSigma_equation": EFFECTIVE_RSIGMA_EQUATION,
        "a_grid": grid.tolist(),
        "radial_terms": {
            "E_CartanGHY": cartan.tolist(),
            "E_HolstNiehYan": holst.tolist(),
            "E_matterFlux": matter.tolist(),
            "E_counterterm": counterterm.tolist(),
        },
        "E_RSigma_residual": residual.tolist(),
        "R_Sigma_solution_residual_max_abs": float(np.max(np.abs(residual))),
        "term_provenance": cleaned_provenance,
    }


def build_rsigma_certificate_from_residual_payload(
    *,
    residual_payload: dict,
    certificate_payload: dict,
    tolerance: float = 1.0e-8,
) -> dict:
    """Merge residual evidence into a strict R_Sigma solution certificate."""

    residual = float(residual_payload["R_Sigma_solution_residual_max_abs"])
    if residual > tolerance:
        raise ValueError("R_Sigma residual exceeds tolerance")
    payload = dict(certificate_payload)
    payload["effective_RSigma_equation"] = residual_payload["effective_RSigma_equation"]
    payload["R_Sigma_solution_residual_max_abs"] = residual
    payload.setdefault("R_Sigma_solution_certificate_type", "conditional_closed_frontier_solution")
    return validate_active_z2sigma_rsigma_solution_certificate(payload)
