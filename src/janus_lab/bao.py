"""BAO prediction helpers."""

from __future__ import annotations

from typing import Callable

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S
from .data import BaoDataset
from .models import ArrayLike, JanusExpansion, _as_array, janus_q0_from_u0


def dimensionless_comoving_integral(
    z: ArrayLike,
    e_func: Callable[[ArrayLike], ArrayLike],
    samples: int = 2048,
) -> ArrayLike:
    """Compute integral_0^z dz'/E(z')."""

    z_arr = _as_array(z)
    flat_z = z_arr.reshape(-1)
    values = np.empty_like(flat_z)
    trapz = getattr(np, "trapezoid", None)
    if trapz is None:
        trapz = np.trapz
    for index, z_value in enumerate(flat_z):
        if z_value == 0:
            values[index] = 0.0
            continue
        grid = np.linspace(0.0, z_value, samples)
        values[index] = trapz(1.0 / _as_array(e_func(grid)), grid)
    result = values.reshape(z_arr.shape)
    if np.isscalar(z):
        return float(np.asarray(result))
    return result


def bao_prediction(
    z: ArrayLike,
    quantity: str,
    e_func: Callable[[ArrayLike], ArrayLike],
    scale: float,
    samples: int = 2048,
) -> ArrayLike:
    """Predict a DESI/Cobaya BAO quantity.

    ``scale`` is c / (H0 * r_d). BAO-only constraints mostly determine this
    combination rather than H0 and r_d separately.
    """

    z_arr = _as_array(z)
    integral = _as_array(dimensionless_comoving_integral(z_arr, e_func, samples=samples))
    e_value = _as_array(e_func(z_arr))

    if quantity == "DM_over_rs":
        prediction = scale * integral
    elif quantity == "DH_over_rs":
        prediction = scale / e_value
    elif quantity == "DV_over_rs":
        prediction = scale * np.cbrt(z_arr * integral**2 / e_value)
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z):
        return float(np.asarray(prediction))
    return prediction


def bao_prediction_vector(
    dataset: BaoDataset,
    e_func: Callable[[ArrayLike], ArrayLike],
    scale: float,
    samples: int = 2048,
) -> np.ndarray:
    """Predict the full BAO vector in dataset order."""

    return np.asarray(
        [
            bao_prediction(z, quantity, e_func, scale=scale, samples=samples)
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def janus_bao_prediction(
    z: ArrayLike,
    quantity: str,
    model: JanusExpansion,
    scale: float,
) -> ArrayLike:
    """Predict BAO quantities using the open Janus distance relation.

    Source: local bibliography M18. Eq. 15-17 give
    r = sinh(2*(u0-u_e)); Eq. 14 gives the a0/H0/q0 conversion used
    for DM_over_rs in the current interpretation.
    """

    z_arr = _as_array(z)
    u_e = _as_array(model.u_of_z(z_arr))
    chi = 2.0 * (model.u0 - u_e)
    marker = np.sinh(chi)
    q0 = janus_q0_from_u0(model.u0)
    dm_over_rs = scale * marker / np.sqrt(1.0 - 2.0 * q0)
    dh_over_rs = scale / _as_array(model.e(z_arr))

    if quantity == "DM_over_rs":
        prediction = dm_over_rs
    elif quantity == "DH_over_rs":
        prediction = dh_over_rs
    elif quantity == "DV_over_rs":
        prediction = np.cbrt(z_arr * dm_over_rs**2 * dh_over_rs)
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z):
        return float(np.asarray(prediction))
    return prediction


def janus_bao_prediction_vector(
    dataset: BaoDataset,
    model: JanusExpansion,
    scale: float,
) -> np.ndarray:
    """Predict the full BAO vector for Janus-specific open geometry."""

    return np.asarray(
        [
            janus_bao_prediction(z, quantity, model, scale=scale)
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def planck_like_scale(h0: float = 67.4, rd_mpc: float = 147.09) -> float:
    """Return c/(H0*rd), a useful Planck-like BAO scale."""

    return SPEED_OF_LIGHT_KM_S / (h0 * rd_mpc)
