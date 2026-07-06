"""Projective stereographic identities for S^n/RP^n."""

from __future__ import annotations

import numpy as np


def antipodal_stereographic_image(x) -> np.ndarray:
    """Return stereographic coordinates of the antipode on the unit sphere.

    If x are stereographic coordinates from one pole, the antipodal map on S^n
    is represented by x -> -x/|x|^2 on the chart where x != 0.
    """

    vector = np.asarray(x, dtype=float)
    if vector.ndim != 1 or vector.size == 0 or not np.all(np.isfinite(vector)):
        raise ValueError("x must be a finite nonempty vector")
    norm2 = float(np.dot(vector, vector))
    if norm2 <= 0.0:
        raise ValueError("stereographic antipodal image is undefined at x=0")
    return -vector / norm2


def antipodal_stereographic_radius(radius: float) -> float:
    r = float(radius)
    if not np.isfinite(r) or r <= 0.0:
        raise ValueError("radius must be positive and finite")
    return 1.0 / r


def reciprocal_radius_fixed_point() -> float:
    return 1.0
