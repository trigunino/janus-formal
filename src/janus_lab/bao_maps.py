"""Candidate BAO observable maps for Janus.

These helpers are intentionally small. They separate the verified Janus base
geometry from phenomenological or partially derived effective-ruler maps.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .models import ArrayLike, JanusExpansion, _as_array, janus_q0_from_u0


BAO_QUANTITIES = ("DM_over_rs", "DH_over_rs", "DV_over_rs")


@dataclass(frozen=True)
class QuantityLinearScale:
    """Quantity-dependent empirical scale S_Q(z)=A_Q+B_Q z."""

    dm_intercept: float
    dm_slope: float
    dh_intercept: float
    dh_slope: float
    dv_intercept: float
    dv_slope: float

    def scale(self, z: ArrayLike, quantity: str) -> ArrayLike:
        z_arr = _as_array(z)
        if quantity == "DM_over_rs":
            value = self.dm_intercept + self.dm_slope * z_arr
        elif quantity == "DH_over_rs":
            value = self.dh_intercept + self.dh_slope * z_arr
        elif quantity == "DV_over_rs":
            value = self.dv_intercept + self.dv_slope * z_arr
        else:
            raise ValueError(f"Unsupported BAO quantity: {quantity}")
        if np.isscalar(z):
            return float(np.asarray(value))
        return value


@dataclass(frozen=True)
class AnisotropicSqrtAScale:
    """C2 candidate: transverse/radial sqrt(a) scales, DV derived."""

    dm_amplitude: float
    dh_amplitude: float

    @property
    def dv_amplitude(self) -> float:
        return float(np.cbrt(self.dm_amplitude**2 * self.dh_amplitude))

    def scale(self, z: ArrayLike, quantity: str) -> ArrayLike:
        if quantity == "DM_over_rs":
            return sqrt_a_scale(z, self.dm_amplitude)
        if quantity == "DH_over_rs":
            return sqrt_a_scale(z, self.dh_amplitude)
        if quantity == "DV_over_rs":
            return sqrt_a_scale(z, self.dv_amplitude)
        raise ValueError(f"Unsupported BAO quantity: {quantity}")


@dataclass(frozen=True)
class AnisotropicPowerLawScale:
    """C2b candidate: transverse/radial power laws, DV derived."""

    dm_amplitude: float
    dm_power: float
    dh_amplitude: float
    dh_power: float

    def dm_scale(self, z: ArrayLike) -> ArrayLike:
        return power_law_scale(z, self.dm_amplitude, self.dm_power)

    def dh_scale(self, z: ArrayLike) -> ArrayLike:
        return power_law_scale(z, self.dh_amplitude, self.dh_power)

    def dv_scale(self, z: ArrayLike) -> ArrayLike:
        z_arr = _as_array(z)
        amplitude = np.cbrt(self.dm_amplitude**2 * self.dh_amplitude)
        power = (2.0 * self.dm_power + self.dh_power) / 3.0
        value = amplitude * (1.0 + z_arr) ** power
        if np.isscalar(z):
            return float(np.asarray(value))
        return value

    def scale(self, z: ArrayLike, quantity: str) -> ArrayLike:
        if quantity == "DM_over_rs":
            return self.dm_scale(z)
        if quantity == "DH_over_rs":
            return self.dh_scale(z)
        if quantity == "DV_over_rs":
            return self.dv_scale(z)
        raise ValueError(f"Unsupported BAO quantity: {quantity}")


def sqrt_a_scale(z: ArrayLike, amplitude: float = 1.0) -> ArrayLike:
    """Gauge toy scale proportional to sqrt(a)=1/sqrt(1+z)."""

    z_arr = _as_array(z)
    value = amplitude / np.sqrt(1.0 + z_arr)
    if np.isscalar(z):
        return float(np.asarray(value))
    return value


def power_law_scale(z: ArrayLike, amplitude: float, power: float) -> ArrayLike:
    """Generic scale A*(1+z)^p used to summarize inferred BAO rulers."""

    z_arr = _as_array(z)
    value = amplitude * (1.0 + z_arr) ** power
    if np.isscalar(z):
        return float(np.asarray(value))
    return value


def linear_scale(z: ArrayLike, intercept: float, slope: float) -> ArrayLike:
    """Generic scale A+B*z used for local ruler diagnostics."""

    z_arr = _as_array(z)
    value = intercept + slope * z_arr
    if np.isscalar(z):
        return float(np.asarray(value))
    return value


def redshift_power_remap(z: ArrayLike, gamma: float) -> ArrayLike:
    """C5 candidate redshift map: 1+z_geom=(1+z_obs)^gamma."""

    if gamma <= 0:
        raise ValueError("gamma must be positive.")
    z_arr = _as_array(z)
    if np.any(z_arr < 0):
        raise ValueError("z must be non-negative.")
    value = (1.0 + z_arr) ** gamma - 1.0
    if np.isscalar(z):
        return float(np.asarray(value))
    return value


def dv_from_dm_dh(dm_over_rs: ArrayLike, dh_over_rs: ArrayLike, z: ArrayLike) -> ArrayLike:
    """Standard compressed BAO relation D_V/r_d=(z DM^2 DH)^(1/3)."""

    z_arr = _as_array(z)
    value = np.cbrt(z_arr * _as_array(dm_over_rs) ** 2 * _as_array(dh_over_rs))
    if np.isscalar(z):
        return float(np.asarray(value))
    return value


def janus_c5_redshift_prediction(
    z_observed: ArrayLike,
    quantity: str,
    model: JanusExpansion,
    scale: float,
    gamma: float,
    compression_z: str = "observed",
) -> ArrayLike:
    """C5 candidate: remap observed redshift before evaluating Janus geometry.

    `compression_z` controls the redshift used in the compressed `D_V` formula:
    `observed` keeps the DESI reported redshift, `geometric` uses remapped z.
    """

    z_obs = _as_array(z_observed)
    z_geom = _as_array(redshift_power_remap(z_obs, gamma))
    u_e = _as_array(model.u_of_z(z_geom))
    marker = np.sinh(2.0 * (model.u0 - u_e))
    q0 = janus_q0_from_u0(model.u0)
    dm_over_rs = scale * marker / np.sqrt(1.0 - 2.0 * q0)
    dh_over_rs = scale / _as_array(model.e(z_geom))
    if compression_z == "observed":
        z_for_dv = z_obs
    elif compression_z == "geometric":
        z_for_dv = z_geom
    else:
        raise ValueError(f"Unsupported compression_z: {compression_z}")

    if quantity == "DM_over_rs":
        prediction = dm_over_rs
    elif quantity == "DH_over_rs":
        prediction = dh_over_rs
    elif quantity == "DV_over_rs":
        prediction = dv_from_dm_dh(dm_over_rs, dh_over_rs, z_for_dv)
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z_observed):
        return float(np.asarray(prediction))
    return prediction


def janus_c6_common_ruler_prediction(
    z: ArrayLike,
    quantity: str,
    model: JanusExpansion,
    scale: float,
    ruler_power: float,
) -> ArrayLike:
    """C6 candidate: common effective BAO ruler `S(z)=scale*(1+z)^p`."""

    z_arr = _as_array(z)
    u_e = _as_array(model.u_of_z(z_arr))
    marker = np.sinh(2.0 * (model.u0 - u_e))
    q0 = janus_q0_from_u0(model.u0)
    common_scale = _as_array(power_law_scale(z_arr, scale, ruler_power))
    dm_over_rs = common_scale * marker / np.sqrt(1.0 - 2.0 * q0)
    dh_over_rs = common_scale / _as_array(model.e(z_arr))

    if quantity == "DM_over_rs":
        prediction = dm_over_rs
    elif quantity == "DH_over_rs":
        prediction = dh_over_rs
    elif quantity == "DV_over_rs":
        prediction = dv_from_dm_dh(dm_over_rs, dh_over_rs, z_arr)
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z):
        return float(np.asarray(prediction))
    return prediction


def janus_c7_anisotropic_linear_ruler_prediction(
    z: ArrayLike,
    quantity: str,
    model: JanusExpansion,
    dm_intercept: float,
    dm_slope: float,
    dh_intercept: float,
    dh_slope: float,
) -> ArrayLike:
    """C7 candidate: linear transverse/radial rulers with `D_V` derived."""

    z_arr = _as_array(z)
    u_e = _as_array(model.u_of_z(z_arr))
    marker = np.sinh(2.0 * (model.u0 - u_e))
    q0 = janus_q0_from_u0(model.u0)
    dm_base = marker / np.sqrt(1.0 - 2.0 * q0)
    dh_base = 1.0 / _as_array(model.e(z_arr))
    dv_base = dv_from_dm_dh(dm_base, dh_base, z_arr)
    dm_scale = _as_array(linear_scale(z_arr, dm_intercept, dm_slope))
    dh_scale = _as_array(linear_scale(z_arr, dh_intercept, dh_slope))
    dv_scale = np.cbrt(dm_scale**2 * dh_scale)

    if quantity == "DM_over_rs":
        prediction = dm_base * dm_scale
    elif quantity == "DH_over_rs":
        prediction = dh_base * dh_scale
    elif quantity == "DV_over_rs":
        prediction = dv_base * dv_scale
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z):
        return float(np.asarray(prediction))
    return prediction


def gauge_weighted_open_marker(
    z: ArrayLike,
    model: JanusExpansion,
    gauge_power: float,
    samples: int = 512,
) -> ArrayLike:
    """Open marker with dchi weighted by a(u)^gauge_power.

    `gauge_power=0` recovers the M18 marker `sinh(2*(u0-u_e))`.
    """

    z_arr = _as_array(z)
    flat_z = z_arr.reshape(-1)
    values = np.empty_like(flat_z)
    a0_shape = model._shape(np.asarray(model.u0))
    trapz = getattr(np, "trapezoid", None)
    if trapz is None:
        trapz = np.trapz
    for index, z_value in enumerate(flat_z):
        ue = float(model.u_of_z(float(z_value)))
        if ue == model.u0:
            values[index] = 0.0
            continue
        grid = np.linspace(ue, model.u0, samples)
        a_norm = model._shape(grid) / a0_shape
        chi = trapz(2.0 * a_norm**gauge_power, grid)
        values[index] = np.sinh(chi)
    result = values.reshape(z_arr.shape)
    if np.isscalar(z):
        return float(np.asarray(result))
    return result


def janus_c4_gauge_prediction(
    z: ArrayLike,
    quantity: str,
    model: JanusExpansion,
    scale: float,
    transverse_power: float,
    radial_power: float,
    samples: int = 512,
) -> ArrayLike:
    """C4 candidate: change BAO observables, not only the ruler.

    `transverse_power` modifies the open-marker null path.
    `radial_power` applies an `a(z)^radial_power` factor to `D_H`.
    """

    z_arr = _as_array(z)
    marker = _as_array(
        gauge_weighted_open_marker(
            z_arr,
            model,
            gauge_power=transverse_power,
            samples=samples,
        )
    )
    q0 = janus_q0_from_u0(model.u0)
    dm_over_rs = scale * marker / np.sqrt(1.0 - 2.0 * q0)
    a_z = 1.0 / (1.0 + z_arr)
    dh_over_rs = scale * a_z**radial_power / _as_array(model.e(z_arr))

    if quantity == "DM_over_rs":
        prediction = dm_over_rs
    elif quantity == "DH_over_rs":
        prediction = dh_over_rs
    elif quantity == "DV_over_rs":
        prediction = dv_from_dm_dh(dm_over_rs, dh_over_rs, z_arr)
    else:
        raise ValueError(f"Unsupported BAO quantity: {quantity}")

    if np.isscalar(z):
        return float(np.asarray(prediction))
    return prediction
