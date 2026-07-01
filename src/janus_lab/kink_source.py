"""Source-side guard for Janus-Holst kink growth jumps."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import numpy as np


ArrayLike = float | np.ndarray
KinkCoefficient = float | Callable[[np.ndarray, np.ndarray], ArrayLike]
AlphaFunction = float | Callable[[np.ndarray], ArrayLike]

ALLOWED_PROVENANCE = {"source_derived_holst_junction", "symbolic_scaffold"}
FORBIDDEN_PROVENANCE = {
    "kids_residual",
    "kids_pair23",
    "kids_delta_z",
    "photoz_fit",
    "bin_factor_fit",
    "amplitude_fit",
    "eta_scan_fit",
    "tilt_scan_fit",
    "kink_fit",
}


def validate_kink_source_provenance(provenance: str) -> str:
    normalized = provenance.strip().lower()
    if normalized in ALLOWED_PROVENANCE:
        return normalized
    if normalized in FORBIDDEN_PROVENANCE or "kids" in normalized or "fit" in normalized:
        raise ValueError(f"forbidden kink-source provenance: {provenance}")
    raise ValueError(f"unknown kink-source provenance: {provenance}")


def _evaluate(value: float | Callable[..., ArrayLike], *args: np.ndarray) -> np.ndarray:
    raw: Any = value(*args) if callable(value) else value
    return np.asarray(raw, dtype=float)


def kink_jump_amplitude(
    k: ArrayLike,
    a: ArrayLike,
    delta: ArrayLike,
    *,
    coefficient: KinkCoefficient,
    alpha: AlphaFunction,
    provenance: str,
) -> np.ndarray:
    """Return Delta(d delta / d ln a) = S_kink(k,a) alpha_Janus(a) delta."""

    validate_kink_source_provenance(provenance)
    k_arr = np.asarray(k, dtype=float)
    a_arr = np.asarray(a, dtype=float)
    delta_arr = np.asarray(delta, dtype=float)
    s_arr = _evaluate(coefficient, k_arr, a_arr)
    alpha_arr = _evaluate(alpha, a_arr)
    out = np.broadcast_arrays(s_arr, alpha_arr, delta_arr)
    jump = out[0] * out[1] * out[2]
    if not np.all(np.isfinite(jump)):
        raise ValueError("kink jump amplitude must be finite.")
    return np.asarray(jump, dtype=float)


def kink_source_status(
    *,
    skink_coefficient_derived: bool,
    alpha_janus_derived: bool,
    provenance: str,
) -> dict:
    normalized = validate_kink_source_provenance(provenance)
    prediction_ready = bool(
        normalized == "source_derived_holst_junction"
        and skink_coefficient_derived
        and alpha_janus_derived
    )
    return {
        "provenance": normalized,
        "skink_coefficient_derived": bool(skink_coefficient_derived),
        "alpha_Janus_derived": bool(alpha_janus_derived),
        "prediction_ready": prediction_ready,
    }
