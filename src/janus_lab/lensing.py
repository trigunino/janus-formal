"""Weak-field lensing diagnostics for the Janus positive sector.

This is a Newtonian-limit source map only. It is not a relativistic ray tracer.
"""

from __future__ import annotations

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S
from .field_statistics import sigma_r_3d
from .models import ArrayLike, JanusExpansion, _as_array, _maybe_scalar, janus_q0_from_u0
from .poisson import (
    effective_density_grid,
    solve_periodic_poisson_2d,
    solve_periodic_poisson_3d,
)
from .signed_sector import Sector


_ALLOWED_LENSING_FACTOR_PROVENANCE = {
    "unity",
    "standard_scaffold",
    "source_derived",
    "declared_qdet_density",
    "negative_proper_density_volume",
    "declared_qcross_projection",
    "positive_geodesic_projection",
    "janus_open_distance",
}

_FORBIDDEN_LENSING_AMPLITUDE_PROVENANCE = {
    "raw_flrw_scale_ratio",
    "scale_ratio_amplitude",
    "det4_metric",
    "det4_metric_plus",
    "det4_metric_minus",
    "weight3_dust",
    "weight3_dust_plus",
    "weight3_dust_minus",
    "weight_pf_plus",
    "weight_pf_minus",
    "survey_fit",
    "shear_fit",
    "sigma8_fit",
    "s8_fit",
}

_ALLOWED_BETA_FIELD_PROVENANCE = {
    "declared_physical_velocity",
    "pm_hubble_calibrated_diagnostic",
    "source_derived_janus_dynamics",
}

_PREDICTIVE_BETA_FIELD_PROVENANCE = {
    "source_derived_janus_dynamics",
}


def validate_lensing_factor_provenance(provenance: str) -> str:
    """Reject raw scale/determinant branches as optical amplitudes."""

    normalized = provenance.strip().lower()
    if normalized in _FORBIDDEN_LENSING_AMPLITUDE_PROVENANCE:
        raise ValueError(
            "raw scale, determinant, and dust-volume ratios are not lensing amplitudes."
        )
    if normalized not in _ALLOWED_LENSING_FACTOR_PROVENANCE:
        raise ValueError("unknown lensing factor provenance.")
    return normalized


def validate_beta_field_provenance(provenance: str) -> str:
    """Accept only declared non-fit beta-field provenance labels."""

    normalized = provenance.strip().lower()
    if normalized in _FORBIDDEN_LENSING_AMPLITUDE_PROVENANCE:
        raise ValueError("beta field provenance cannot be a fitted lensing amplitude.")
    if normalized not in _ALLOWED_BETA_FIELD_PROVENANCE:
        raise ValueError("unknown beta field provenance.")
    return normalized


def beta_field_is_prediction_ready(provenance: str) -> bool:
    """Whether a beta field is source-derived enough for prediction use."""

    return validate_beta_field_provenance(provenance) in _PREDICTIVE_BETA_FIELD_PROVENANCE


def positive_photon_lensing_source_grid(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    *,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Source density seen by positive-energy photons in the weak-field limit."""

    source = effective_density_grid(
        positive_density_abs,
        negative_density_abs,
        Sector.POSITIVE,
    )
    if subtract_mean:
        return source - float(np.mean(source))
    return source


def flrw_metric_determinant_ratio_factor(
    scale_factor_plus: ArrayLike,
    scale_factor_minus: ArrayLike,
) -> ArrayLike:
    """FLRW determinant factor `sqrt(-g_-/-g_+)=(a_-/a_+)^4`."""

    plus = _as_array(scale_factor_plus)
    minus = _as_array(scale_factor_minus)
    if np.any(plus <= 0.0) or np.any(minus <= 0.0):
        raise ValueError("scale factors must be positive.")
    ratio = (minus / plus) ** 4
    if np.ndim(ratio) == 0:
        return float(ratio)
    return ratio


def cross_sector_optical_projection_factor(
    projection_plus: ArrayLike,
    projection_minus: ArrayLike,
) -> ArrayLike:
    """Cross projection ratio `Q_cross=A_-/A_+` for positive photons."""

    plus = _as_array(projection_plus)
    minus = _as_array(projection_minus)
    if np.any(plus <= 0.0) or np.any(minus <= 0.0):
        raise ValueError("optical projections must be positive.")
    ratio = minus / plus
    if np.ndim(ratio) == 0:
        return float(ratio)
    return ratio


def equal_comoving_cross_projection_factor(z: ArrayLike) -> ArrayLike:
    """Equal-projection FLRW limit for `Q_cross`."""

    z_arr = _as_array(z)
    if np.any(z_arr < 0.0):
        raise ValueError("z must be non-negative.")
    factor = np.ones_like(z_arr, dtype=float)
    return _maybe_scalar(z, factor)


def relative_velocity_cross_projection_factor(
    beta_magnitude: ArrayLike,
    beta_parallel: ArrayLike,
) -> ArrayLike:
    """Local orthonormal-frame `Q_cross=gamma^2(1-beta_parallel)^2`."""

    beta = _as_array(beta_magnitude)
    parallel = _as_array(beta_parallel)
    if np.any(beta < 0.0) or np.any(beta >= 1.0):
        raise ValueError("beta_magnitude must satisfy 0 <= beta < 1.")
    if np.any(np.abs(parallel) > beta):
        raise ValueError("|beta_parallel| must not exceed beta_magnitude.")
    gamma_squared = 1.0 / (1.0 - beta**2)
    factor = gamma_squared * (1.0 - parallel) ** 2
    if np.ndim(factor) == 0:
        return float(factor)
    return factor


def relative_velocity_cross_projection_from_vectors(
    beta_vectors: np.ndarray,
    photon_direction: np.ndarray,
) -> np.ndarray:
    """`Q_cross` from beta vectors and a positive-photon spatial direction."""

    beta = np.asarray(beta_vectors, dtype=float)
    direction = np.asarray(photon_direction, dtype=float)
    if beta.ndim == 0:
        raise ValueError("beta_vectors must have a vector component axis.")
    if direction.ndim != 1:
        raise ValueError("photon_direction must be one-dimensional.")
    if beta.shape[-1] != direction.shape[0]:
        raise ValueError("photon_direction length must match beta vector dimension.")
    norm = float(np.linalg.norm(direction))
    if norm <= 0.0:
        raise ValueError("photon_direction must be non-zero.")
    unit_direction = direction / norm
    beta_magnitude = np.linalg.norm(beta, axis=-1)
    beta_parallel = np.tensordot(beta, unit_direction, axes=([-1], [0]))
    return np.asarray(
        relative_velocity_cross_projection_factor(beta_magnitude, beta_parallel),
        dtype=float,
    )


def lorentz_gamma_from_beta_vectors(beta_vectors: np.ndarray) -> np.ndarray:
    """Lorentz gamma for a field of local beta vectors."""

    beta = np.asarray(beta_vectors, dtype=float)
    if beta.ndim == 0:
        raise ValueError("beta_vectors must have a vector component axis.")
    beta2 = np.sum(beta**2, axis=-1)
    if np.any(beta2 >= 1.0):
        raise ValueError("beta vector magnitude must be smaller than 1.")
    return 1.0 / np.sqrt(1.0 - beta2)


def transported_four_velocity_from_beta_vectors(beta_vectors: np.ndarray) -> np.ndarray:
    """Local positive-frame four-velocity `u^A=gamma(1,beta_vec)`."""

    beta = np.asarray(beta_vectors, dtype=float)
    gamma = lorentz_gamma_from_beta_vectors(beta)
    return np.concatenate([gamma[..., np.newaxis], gamma[..., np.newaxis] * beta], axis=-1)


def boosted_perfect_fluid_t00_source(
    density_abs: np.ndarray,
    beta_vectors: np.ndarray,
    *,
    pressure_abs: float | np.ndarray = 0.0,
    pi00: float | np.ndarray = 0.0,
) -> np.ndarray:
    """Local boosted `T00=(rho+p)gamma^2-p+Pi00` for source diagnostics."""

    density = np.asarray(density_abs, dtype=float)
    pressure = np.asarray(pressure_abs, dtype=float)
    pi = np.asarray(pi00, dtype=float)
    if np.any(density < 0.0) or np.any(pressure < 0.0):
        raise ValueError("density_abs and pressure_abs must be non-negative.")
    gamma = lorentz_gamma_from_beta_vectors(beta_vectors)
    try:
        return (density + pressure) * gamma**2 - pressure + pi
    except ValueError as exc:
        raise ValueError("density, pressure, pi00 and beta grid must broadcast.") from exc


def positive_noncomoving_t00_source_grid(
    positive_density_abs: np.ndarray,
    negative_density_eff_abs: np.ndarray,
    negative_beta_vectors: np.ndarray,
    *,
    negative_pressure_eff_abs: float | np.ndarray = 0.0,
    negative_pi00_eff: float | np.ndarray = 0.0,
    beta_field_provenance: str = "declared_physical_velocity",
    subtract_mean: bool = True,
) -> np.ndarray:
    """Positive-frame non-comoving scalar source using boosted negative `T00`."""

    validate_beta_field_provenance(beta_field_provenance)
    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_eff_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    if np.any(positive < 0.0) or np.any(negative < 0.0):
        raise ValueError("density grids must be non-negative.")
    boosted_negative = boosted_perfect_fluid_t00_source(
        negative,
        negative_beta_vectors,
        pressure_abs=negative_pressure_eff_abs,
        pi00=negative_pi00_eff,
    )
    source = positive - boosted_negative
    if subtract_mean:
        return source - float(np.mean(source))
    return source


def velocity_km_s_to_beta_vectors(
    velocity_vectors_km_s: np.ndarray,
    speed_of_light_km_s: float = SPEED_OF_LIGHT_KM_S,
) -> np.ndarray:
    """Convert physical velocity vectors in km/s to dimensionless beta vectors."""

    if speed_of_light_km_s <= 0.0:
        raise ValueError("speed_of_light_km_s must be positive.")
    velocities = np.asarray(velocity_vectors_km_s, dtype=float)
    if velocities.ndim == 0:
        raise ValueError("velocity_vectors_km_s must have a vector component axis.")
    beta = velocities / speed_of_light_km_s
    if np.any(np.linalg.norm(beta, axis=-1) >= 1.0):
        raise ValueError("velocity magnitude must be smaller than the speed of light.")
    return beta


def relative_velocity_cross_projection_from_velocities_km_s(
    velocity_vectors_km_s: np.ndarray,
    photon_direction: np.ndarray,
    speed_of_light_km_s: float = SPEED_OF_LIGHT_KM_S,
) -> np.ndarray:
    """`Q_cross` from physical velocity vectors in km/s and photon direction."""

    beta = velocity_km_s_to_beta_vectors(
        velocity_vectors_km_s,
        speed_of_light_km_s=speed_of_light_km_s,
    )
    return relative_velocity_cross_projection_from_vectors(beta, photon_direction)


def positive_effective_negative_density(
    negative_density_proper_abs: np.ndarray,
    determinant_ratio: ArrayLike,
) -> np.ndarray:
    """Negative proper density mapped into the positive-sector effective source."""

    negative = np.asarray(negative_density_proper_abs, dtype=float)
    if np.any(negative < 0.0):
        raise ValueError("negative proper density must be non-negative.")
    determinant = np.asarray(determinant_ratio, dtype=float)
    if np.any(determinant <= 0.0):
        raise ValueError("determinant ratio must be positive.")
    try:
        return determinant * negative
    except ValueError as exc:
        raise ValueError("determinant ratio must broadcast to density grid.") from exc


def negative_sector_lensing_weight_factor(
    *,
    negative_density_convention: str = "positive_effective",
    determinant_ratio: ArrayLike = 1.0,
    cross_projection_ratio: ArrayLike = 1.0,
    determinant_ratio_provenance: str = "negative_proper_density_volume",
    cross_projection_ratio_provenance: str = "declared_qcross_projection",
) -> ArrayLike:
    """Total weight multiplying negative density in the positive optical source."""

    validate_lensing_factor_provenance(cross_projection_ratio_provenance)
    cross = np.asarray(cross_projection_ratio, dtype=float)
    if np.any(cross <= 0.0):
        raise ValueError("cross projection ratio must be positive.")
    if negative_density_convention == "positive_effective":
        weight = cross
    elif negative_density_convention == "negative_proper":
        validate_lensing_factor_provenance(determinant_ratio_provenance)
        determinant = np.asarray(determinant_ratio, dtype=float)
        if np.any(determinant <= 0.0):
            raise ValueError("determinant ratio must be positive.")
        weight = determinant * cross
    else:
        raise ValueError(
            "negative_density_convention must be 'positive_effective' or 'negative_proper'."
        )
    if np.ndim(weight) == 0:
        return float(weight)
    return weight


def positive_photon_lensing_source_grid_with_density_convention(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    *,
    negative_density_convention: str = "positive_effective",
    determinant_ratio: ArrayLike = 1.0,
    cross_projection_ratio: ArrayLike = 1.0,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Positive-sheet source with explicit negative-density volume convention."""

    ratio = negative_sector_lensing_weight_factor(
        negative_density_convention=negative_density_convention,
        determinant_ratio=determinant_ratio,
        cross_projection_ratio=cross_projection_ratio,
    )
    return positive_photon_lensing_source_grid_with_determinant_ratio(
        positive_density_abs,
        negative_density_abs,
        ratio,
        subtract_mean=subtract_mean,
    )


def positive_photon_lensing_source_grid_with_determinant_ratio(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    determinant_ratio: ArrayLike,
    *,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Positive-sheet source `rho_+ - B |rho_-|` with determinant factor B."""

    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    if np.any(positive < 0.0) or np.any(negative < 0.0):
        raise ValueError("absolute density grids must be non-negative.")
    ratio = np.asarray(determinant_ratio, dtype=float)
    if np.any(ratio <= 0.0):
        raise ValueError("determinant ratio must be positive.")
    try:
        source = positive - ratio * negative
    except ValueError as exc:
        raise ValueError("determinant ratio must broadcast to density grids.") from exc
    if subtract_mean:
        return source - float(np.mean(source))
    return source


def positive_photon_lensing_contrast(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
) -> np.ndarray:
    """Centered Janus lensing source normalized by total absolute mean density."""

    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    if np.any(positive < 0.0) or np.any(negative < 0.0):
        raise ValueError("absolute density grids must be non-negative.")
    scale = float(np.mean(positive + negative))
    if scale <= 0.0:
        raise ValueError("total density mean must be positive.")
    source = positive_photon_lensing_source_grid(positive, negative)
    return source / scale


def positive_photon_lensing_contrast_with_determinant_ratio(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    determinant_ratio: ArrayLike,
) -> np.ndarray:
    """Centered lensing contrast for `rho_+ - B |rho_-|`."""

    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    scale = float(np.mean(positive + negative))
    if scale <= 0.0:
        raise ValueError("total density mean must be positive.")
    source = positive_photon_lensing_source_grid_with_determinant_ratio(
        positive,
        negative,
        determinant_ratio,
    )
    return source / scale


def positive_photon_lensing_contrast_with_density_convention(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    *,
    negative_density_convention: str = "positive_effective",
    determinant_ratio: ArrayLike = 1.0,
    cross_projection_ratio: ArrayLike = 1.0,
) -> np.ndarray:
    """Centered lensing contrast with explicit negative-density convention."""

    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    scale = float(np.mean(positive + negative))
    if scale <= 0.0:
        raise ValueError("total density mean must be positive.")
    source = positive_photon_lensing_source_grid_with_density_convention(
        positive,
        negative,
        negative_density_convention=negative_density_convention,
        determinant_ratio=determinant_ratio,
        cross_projection_ratio=cross_projection_ratio,
    )
    return source / scale


def positive_photon_lensing_potential_2d(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    box_size: float,
    gravitational_constant: float = 1.0,
) -> np.ndarray:
    """Periodic 2D weak-field potential for positive-sector photon diagnostics."""

    source = positive_photon_lensing_source_grid(
        positive_density_abs,
        negative_density_abs,
        subtract_mean=False,
    )
    return solve_periodic_poisson_2d(
        source,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
        subtract_mean=True,
    )


def positive_photon_lensing_potential_3d(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    box_size: float,
    gravitational_constant: float = 1.0,
) -> np.ndarray:
    """Periodic 3D weak-field potential for positive-sector photon diagnostics."""

    source = positive_photon_lensing_source_grid(
        positive_density_abs,
        negative_density_abs,
        subtract_mean=False,
    )
    return solve_periodic_poisson_3d(
        source,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
        subtract_mean=True,
    )


def positive_photon_lensing_sigma_r_3d(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    box_size: float,
    radius: float,
) -> float:
    """RMS of the positive-sector weak-lensing source smoothed at radius."""

    return sigma_r_3d(
        positive_photon_lensing_contrast(positive_density_abs, negative_density_abs),
        box_size=box_size,
        radius=radius,
    )


def project_lensing_contrast_2d(
    lensing_contrast_3d: np.ndarray,
    *,
    axis: int = 2,
    weights: np.ndarray | None = None,
) -> np.ndarray:
    """Project a 3D lensing source into a normalized 2D convergence proxy."""

    values = np.asarray(lensing_contrast_3d, dtype=float)
    if values.ndim != 3:
        raise ValueError("lensing_contrast_3d must be three-dimensional.")
    if axis < 0:
        axis += values.ndim
    if axis < 0 or axis >= values.ndim:
        raise ValueError("axis is out of range.")
    if weights is None:
        return np.mean(values, axis=axis)

    kernel = np.asarray(weights, dtype=float)
    if kernel.ndim != 1:
        raise ValueError("weights must be one-dimensional.")
    if kernel.shape[0] != values.shape[axis]:
        raise ValueError("weights length must match the projected axis.")
    if np.any(kernel < 0.0):
        raise ValueError("weights must be non-negative.")
    total = float(np.sum(kernel))
    if total <= 0.0:
        raise ValueError("weights sum must be positive.")
    normalized = kernel / total
    return np.tensordot(values, normalized, axes=([axis], [0]))


def positive_photon_convergence_proxy_2d(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    *,
    axis: int = 2,
    weights: np.ndarray | None = None,
) -> np.ndarray:
    """Projected weak-field convergence proxy for positive-sector photons."""

    return project_lensing_contrast_2d(
        positive_photon_lensing_contrast(positive_density_abs, negative_density_abs),
        axis=axis,
        weights=weights,
    )


def negative_mass_sphere_reduced_deflection_profile(
    impact_radius: ArrayLike,
    sphere_radius: float,
    amplitude: float = 1.0,
) -> ArrayLike:
    """Reduced negative-lens deflection profile for a uniform negative sphere.

    This follows the source-described dipole-repeller target: zero at the
    center, maximum at grazing impact, and exterior decay as `1/b`.
    """

    if sphere_radius <= 0.0:
        raise ValueError("sphere_radius must be positive.")
    if amplitude < 0.0:
        raise ValueError("amplitude must be non-negative.")
    impact = _as_array(impact_radius)
    if np.any(impact < 0.0):
        raise ValueError("impact_radius must be non-negative.")
    reduced_radius = impact / sphere_radius
    shape = np.empty_like(reduced_radius, dtype=float)
    inside = reduced_radius <= 1.0
    shape[inside] = reduced_radius[inside] ** 2
    shape[~inside] = 1.0 / reduced_radius[~inside]
    value = -amplitude * shape
    return _maybe_scalar(impact_radius, value)


def negative_mass_sphere_annular_dimming_profile(
    impact_radius: ArrayLike,
    sphere_radius: float,
    amplitude: float = 1.0,
) -> ArrayLike:
    """Positive attenuation proxy from the reduced negative-sphere deflection."""

    value = -_as_array(
        negative_mass_sphere_reduced_deflection_profile(
            impact_radius,
            sphere_radius,
            amplitude=amplitude,
        )
    )
    return _maybe_scalar(impact_radius, value)


def negative_mass_sphere_annular_dimming_map(
    x_coordinates: np.ndarray,
    y_coordinates: np.ndarray,
    *,
    sphere_radius: float,
    amplitude: float = 1.0,
    center_x: float = 0.0,
    center_y: float = 0.0,
) -> np.ndarray:
    """2D relative dimming map for a projected uniform negative-mass sphere."""

    x_values = np.asarray(x_coordinates, dtype=float)
    y_values = np.asarray(y_coordinates, dtype=float)
    if x_values.shape != y_values.shape:
        raise ValueError("x_coordinates and y_coordinates must have the same shape.")
    impact = np.sqrt((x_values - center_x) ** 2 + (y_values - center_y) ** 2)
    return np.asarray(
        negative_mass_sphere_annular_dimming_profile(
            impact,
            sphere_radius=sphere_radius,
            amplitude=amplitude,
        ),
        dtype=float,
    )


def janus_open_marker_distance(z: ArrayLike, model: JanusExpansion) -> ArrayLike:
    """Open marker distance `r=sinh(2*(u0-u_e))` from M18 Eqs. 15-17."""

    z_arr = _as_array(z)
    u_e = _as_array(model.u_of_z(z_arr))
    marker = np.sinh(2.0 * (model.u0 - u_e))
    return _maybe_scalar(z, marker)


def janus_open_chi(z: ArrayLike, model: JanusExpansion) -> ArrayLike:
    """Open radial coordinate `chi=2*(u0-u(z))` from M18."""

    z_arr = _as_array(z)
    u_e = _as_array(model.u_of_z(z_arr))
    return _maybe_scalar(z, 2.0 * (model.u0 - u_e))


def janus_curvature_radius_mpc(model: JanusExpansion, h0_km_s_mpc: float) -> float:
    """Curvature radius scale from M18 Eq. 14, in Mpc."""

    if h0_km_s_mpc <= 0.0:
        raise ValueError("h0_km_s_mpc must be positive.")
    q0 = janus_q0_from_u0(model.u0)
    return float(SPEED_OF_LIGHT_KM_S / (h0_km_s_mpc * np.sqrt(1.0 - 2.0 * q0)))


def janus_open_transverse_distance_mpc(
    z: ArrayLike,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> ArrayLike:
    """Janus open transverse comoving distance scale in Mpc."""

    radius = janus_curvature_radius_mpc(model, h0_km_s_mpc)
    return _maybe_scalar(z, radius * _as_array(janus_open_marker_distance(z, model)))


def janus_open_angular_diameter_distance_mpc(
    z: ArrayLike,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> ArrayLike:
    """Janus positive-FLRW angular diameter distance `D_A=D_M/(1+z)`."""

    z_arr = _as_array(z)
    if np.any(z_arr < 0.0):
        raise ValueError("z must be non-negative.")
    transverse = _as_array(janus_open_transverse_distance_mpc(z_arr, model, h0_km_s_mpc))
    return _maybe_scalar(z, transverse / (1.0 + z_arr))


def janus_open_angular_diameter_distance_between_mpc(
    z_lens: ArrayLike,
    z_source: float,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> ArrayLike:
    """Angular diameter distance from a lens plane to a source plane."""

    if z_source <= 0.0:
        raise ValueError("z_source must be positive.")
    if z_source > model.z_max:
        raise ValueError("z_source exceeds model z_max.")
    z_arr = _as_array(z_lens)
    if np.any(z_arr < 0.0):
        raise ValueError("z_lens must be non-negative.")
    chi_lens = _as_array(janus_open_chi(np.minimum(z_arr, z_source), model))
    chi_source = float(janus_open_chi(float(z_source), model))
    radius = janus_curvature_radius_mpc(model, h0_km_s_mpc)
    distance = radius * np.sinh(np.maximum(chi_source - chi_lens, 0.0)) / (1.0 + z_source)
    distance = np.where(z_arr < z_source, distance, 0.0)
    return _maybe_scalar(z_lens, distance)


def janus_open_comoving_lensing_distance_kernel_mpc(
    z_lens: ArrayLike,
    z_source: float,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> ArrayLike:
    """Comoving open-distance lensing kernel `D_M,l D_M,ls / D_M,s`."""

    if z_source <= 0.0:
        raise ValueError("z_source must be positive.")
    if z_source > model.z_max:
        raise ValueError("z_source exceeds model z_max.")
    z_arr = _as_array(z_lens)
    if np.any(z_arr < 0.0):
        raise ValueError("z_lens must be non-negative.")
    chi_lens = _as_array(janus_open_chi(np.minimum(z_arr, z_source), model))
    chi_source = float(janus_open_chi(float(z_source), model))
    radius = janus_curvature_radius_mpc(model, h0_km_s_mpc)
    transverse_lens = radius * np.sinh(chi_lens)
    transverse_source = radius * np.sinh(chi_source)
    transverse_lens_source = radius * np.sinh(np.maximum(chi_source - chi_lens, 0.0))
    kernel = transverse_lens * transverse_lens_source / transverse_source
    kernel = np.where(z_arr < z_source, kernel, 0.0)
    return _maybe_scalar(z_lens, kernel)


def janus_open_angular_lensing_distance_kernel_mpc(
    z_lens: ArrayLike,
    z_source: float,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> ArrayLike:
    """Angular-distance lensing kernel `D_A,l D_A,ls / D_A,s`."""

    z_arr = _as_array(z_lens)
    comoving = _as_array(
        janus_open_comoving_lensing_distance_kernel_mpc(z_arr, z_source, model, h0_km_s_mpc)
    )
    return _maybe_scalar(z_lens, comoving / (1.0 + z_arr))


def janus_open_lensing_geometry_kernel(
    z_lens: ArrayLike,
    z_source: float,
    model: JanusExpansion,
) -> ArrayLike:
    """Geometric lensing kernel from the Janus open marker distance.

    This is only the distance factor `r_l * r_ls / r_s`; it omits growth,
    source distribution, shear estimator and survey normalization.
    """

    if z_source <= 0.0:
        raise ValueError("z_source must be positive.")
    z_arr = _as_array(z_lens)
    if np.any(z_arr < 0.0):
        raise ValueError("z_lens must be non-negative.")
    if z_source > model.z_max:
        raise ValueError("z_source exceeds model z_max.")

    u_lens = _as_array(model.u_of_z(np.minimum(z_arr, z_source)))
    u_source = float(model.u_of_z(z_source))
    chi_lens = 2.0 * (model.u0 - u_lens)
    chi_source = 2.0 * (model.u0 - u_source)
    r_lens = np.sinh(chi_lens)
    r_source = np.sinh(chi_source)
    r_lens_source = np.sinh(np.maximum(chi_source - chi_lens, 0.0))
    kernel = r_lens * r_lens_source / r_source
    kernel = np.where(z_arr < z_source, kernel, 0.0)
    return _maybe_scalar(z_lens, kernel)


def janus_tomographic_lensing_weights(
    z_slices: np.ndarray,
    z_source: float,
    model: JanusExpansion,
) -> np.ndarray:
    """Normalized non-negative Janus open-distance weights for projection."""

    z_values = np.asarray(z_slices, dtype=float)
    if z_values.ndim != 1:
        raise ValueError("z_slices must be one-dimensional.")
    kernel = np.asarray(
        janus_open_lensing_geometry_kernel(z_values, z_source, model),
        dtype=float,
    )
    total = float(np.sum(kernel))
    if total <= 0.0:
        raise ValueError("lensing kernel has zero weight.")
    return kernel / total


def _normalized_source_weights(
    source_redshifts: np.ndarray,
    source_weights: np.ndarray,
    model: JanusExpansion,
) -> tuple[np.ndarray, np.ndarray]:
    redshifts = np.asarray(source_redshifts, dtype=float)
    weights = np.asarray(source_weights, dtype=float)
    if redshifts.ndim != 1 or weights.ndim != 1:
        raise ValueError("source redshifts and weights must be one-dimensional.")
    if redshifts.shape != weights.shape:
        raise ValueError("source redshifts and weights must have the same shape.")
    if redshifts.size == 0:
        raise ValueError("source distribution must not be empty.")
    if np.any(redshifts <= 0.0):
        raise ValueError("source redshifts must be positive.")
    if np.any(redshifts > model.z_max):
        raise ValueError("source redshift exceeds model z_max.")
    if np.any(weights < 0.0):
        raise ValueError("source weights must be non-negative.")
    total = float(np.sum(weights))
    if total <= 0.0:
        raise ValueError("source weights sum must be positive.")
    return redshifts, weights / total


def janus_source_distribution_lensing_kernel(
    z_lens: ArrayLike,
    source_redshifts: np.ndarray,
    source_weights: np.ndarray,
    model: JanusExpansion,
) -> ArrayLike:
    """Janus open-distance kernel integrated over an explicit source distribution."""

    redshifts, weights = _normalized_source_weights(source_redshifts, source_weights, model)
    z_arr = _as_array(z_lens)
    kernel = np.zeros_like(z_arr, dtype=float)
    for source_z, source_weight in zip(redshifts, weights):
        kernel += source_weight * _as_array(
            janus_open_lensing_geometry_kernel(z_arr, float(source_z), model)
        )
    return _maybe_scalar(z_lens, kernel)


def janus_source_distribution_lensing_weights(
    z_slices: np.ndarray,
    source_redshifts: np.ndarray,
    source_weights: np.ndarray,
    model: JanusExpansion,
) -> np.ndarray:
    """Normalized projection weights for an explicit Janus source distribution."""

    z_values = np.asarray(z_slices, dtype=float)
    if z_values.ndim != 1:
        raise ValueError("z_slices must be one-dimensional.")
    kernel = np.asarray(
        janus_source_distribution_lensing_kernel(
            z_values,
            source_redshifts,
            source_weights,
            model,
        ),
        dtype=float,
    )
    total = float(np.sum(kernel))
    if total <= 0.0:
        raise ValueError("source-distribution lensing kernel has zero weight.")
    return kernel / total


def _line_of_sight_widths_mpc(
    z_slices: np.ndarray,
    model: JanusExpansion,
    h0_km_s_mpc: float,
) -> np.ndarray:
    z_values = np.asarray(z_slices, dtype=float)
    if z_values.ndim != 1:
        raise ValueError("z_slices must be one-dimensional.")
    if z_values.size < 2:
        raise ValueError("at least two z_slices are required.")
    if np.any(np.diff(z_values) <= 0.0):
        raise ValueError("z_slices must be strictly increasing.")
    chi = np.asarray(janus_open_chi(z_values, model), dtype=float)
    radius = janus_curvature_radius_mpc(model, h0_km_s_mpc)
    edges = np.empty(z_values.size + 1, dtype=float)
    edges[1:-1] = 0.5 * (chi[:-1] + chi[1:])
    edges[0] = max(0.0, chi[0] - 0.5 * (chi[1] - chi[0]))
    edges[-1] = chi[-1] + 0.5 * (chi[-1] - chi[-2])
    return radius * np.diff(edges)


def standard_weak_lensing_prefactor(h0_km_s_mpc: float, omega_abs: float) -> float:
    """Standard dust weak-lensing prefactor kept explicit as a replaceable scaffold."""

    if h0_km_s_mpc <= 0.0:
        raise ValueError("h0_km_s_mpc must be positive.")
    if omega_abs <= 0.0:
        raise ValueError("omega_abs must be positive.")
    return 1.5 * omega_abs * (h0_km_s_mpc / SPEED_OF_LIGHT_KM_S) ** 2


def janus_tensor_lensing_prefactor(
    h0_km_s_mpc: float,
    omega_abs: float,
    *,
    source_factor: ArrayLike = 1.0,
    determinant_ratio: ArrayLike = 1.0,
    cross_projection_ratio: ArrayLike = 1.0,
    projection_factor: ArrayLike = 1.0,
    distance_factor: ArrayLike = 1.0,
    source_factor_provenance: str = "source_derived",
    determinant_ratio_provenance: str = "declared_qdet_density",
    cross_projection_ratio_provenance: str = "declared_qcross_projection",
    projection_factor_provenance: str = "positive_geodesic_projection",
    distance_factor_provenance: str = "janus_open_distance",
) -> ArrayLike:
    """Factorized Janus working prefactor without fitted scalar corrections."""

    for provenance in (
        source_factor_provenance,
        determinant_ratio_provenance,
        cross_projection_ratio_provenance,
        projection_factor_provenance,
        distance_factor_provenance,
    ):
        validate_lensing_factor_provenance(provenance)
    factors = [
        _as_array(source_factor),
        _as_array(determinant_ratio),
        _as_array(cross_projection_ratio),
        _as_array(projection_factor),
        _as_array(distance_factor),
    ]
    if any(np.any(factor <= 0.0) for factor in factors):
        raise ValueError("lensing normalization factors must be positive.")
    value = standard_weak_lensing_prefactor(h0_km_s_mpc, omega_abs)
    for factor in factors:
        value = value * factor
    if np.ndim(value) == 0:
        return float(value)
    return value


def standard_dust_lensing_projection_factor(z: ArrayLike) -> ArrayLike:
    """Standard convergence integrand factor `1/a = 1+z`, kept replaceable."""

    z_arr = _as_array(z)
    if np.any(z_arr < 0.0):
        raise ValueError("z must be non-negative.")
    return _maybe_scalar(z, 1.0 + z_arr)


def positive_flrw_photon_energy_factor(z: ArrayLike) -> ArrayLike:
    """Positive FLRW null-geodesic energy scaling `E(z)/E0 = 1+z`."""

    z_arr = _as_array(z)
    if np.any(z_arr < 0.0):
        raise ValueError("z must be non-negative.")
    return _maybe_scalar(z, 1.0 + z_arr)


def positive_flrw_ricci_projection_factor(z: ArrayLike) -> ArrayLike:
    """Raw Ricci focusing projection `(u.k)^2` relative to today."""

    energy = _as_array(positive_flrw_photon_energy_factor(z))
    return _maybe_scalar(z, energy**2)


def positive_flrw_jacobi_reduced_projection_factor(z: ArrayLike) -> ArrayLike:
    """FLRW Jacobi reduction of density, Ricci projection and affine conversion."""

    return standard_dust_lensing_projection_factor(z)


def janus_absolute_lensing_coefficients(
    z_slices: np.ndarray,
    source_redshifts: np.ndarray,
    source_weights: np.ndarray,
    model: JanusExpansion,
    h0_km_s_mpc: float,
    omega_abs: float,
) -> np.ndarray:
    """Discrete absolute weak-lensing coefficients for `delta_lens_plus`.

    Uses the standard weak-lensing prefactor with the Janus signed source and
    M18 open-distance geometry.
    """

    z_values = np.asarray(z_slices, dtype=float)
    redshifts, weights = _normalized_source_weights(source_redshifts, source_weights, model)
    kernel_mpc = np.zeros_like(z_values, dtype=float)
    for source_z, source_weight in zip(redshifts, weights):
        kernel_mpc += source_weight * _as_array(
            janus_open_comoving_lensing_distance_kernel_mpc(
                z_values,
                float(source_z),
                model,
                h0_km_s_mpc,
            )
        )
    widths_mpc = _line_of_sight_widths_mpc(z_values, model, h0_km_s_mpc)
    prefactor = standard_weak_lensing_prefactor(h0_km_s_mpc, omega_abs)
    projection = np.asarray(positive_flrw_jacobi_reduced_projection_factor(z_values), dtype=float)
    return prefactor * widths_mpc * projection * kernel_mpc


def project_lensing_contrast_2d_with_coefficients(
    lensing_contrast_3d: np.ndarray,
    coefficients: np.ndarray,
    *,
    axis: int = 2,
) -> np.ndarray:
    """Project with absolute coefficients without renormalizing them."""

    values = np.asarray(lensing_contrast_3d, dtype=float)
    coeff = np.asarray(coefficients, dtype=float)
    if values.ndim != 3:
        raise ValueError("lensing_contrast_3d must be three-dimensional.")
    if axis < 0:
        axis += values.ndim
    if axis < 0 or axis >= values.ndim:
        raise ValueError("axis is out of range.")
    if coeff.ndim != 1 or coeff.shape[0] != values.shape[axis]:
        raise ValueError("coefficients length must match the projected axis.")
    return np.tensordot(values, coeff, axes=([axis], [0]))


def shear_from_convergence_proxy_2d(
    convergence: np.ndarray,
    box_size: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Return weak-lensing shear proxy components from a 2D convergence map."""

    kappa = np.asarray(convergence, dtype=float)
    if kappa.ndim != 2:
        raise ValueError("convergence must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny = kappa.shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kkx, kky = np.meshgrid(kx, ky, indexing="ij")
    k2 = kkx**2 + kky**2
    kappa_hat = np.fft.fftn(kappa - float(np.mean(kappa)))
    gamma1_hat = np.zeros_like(kappa_hat, dtype=complex)
    gamma2_hat = np.zeros_like(kappa_hat, dtype=complex)
    nonzero = k2 > 0.0
    gamma1_hat[nonzero] = ((kkx[nonzero] ** 2 - kky[nonzero] ** 2) / k2[nonzero]) * kappa_hat[
        nonzero
    ]
    gamma2_hat[nonzero] = (2.0 * kkx[nonzero] * kky[nonzero] / k2[nonzero]) * kappa_hat[
        nonzero
    ]
    return np.real(np.fft.ifftn(gamma1_hat)), np.real(np.fft.ifftn(gamma2_hat))


def weak_field_weyl_screen_tidal_components_2d(
    lensing_potential: np.ndarray,
    box_size: float,
) -> dict[str, np.ndarray]:
    """Return 2D weak-field screen Hessian components from a metric potential.

    This is a diagnostic operator for a declared weak-field metric potential,
    not a derivation of that potential from the full Janus tensor equations.
    """

    potential = np.asarray(lensing_potential, dtype=float)
    if potential.ndim != 2:
        raise ValueError("lensing_potential must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny = potential.shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kkx, kky = np.meshgrid(kx, ky, indexing="ij")
    potential_hat = np.fft.fftn(potential - float(np.mean(potential)))
    dxx = np.real(np.fft.ifftn(-(kkx**2) * potential_hat))
    dyy = np.real(np.fft.ifftn(-(kky**2) * potential_hat))
    dxy = np.real(np.fft.ifftn(-(kkx * kky) * potential_hat))
    convergence = 0.5 * (dxx + dyy)
    gamma1 = 0.5 * (dxx - dyy)
    gamma2 = dxy
    return {
        "convergence": convergence,
        "gamma1": gamma1,
        "gamma2": gamma2,
        "trace": dxx + dyy,
        "weyl_trace_free_norm": np.sqrt(gamma1**2 + gamma2**2),
    }


def positive_photon_weak_field_weyl_components_2d(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    box_size: float,
    *,
    gravitational_constant: float = 1.0,
    source_provenance: str = "source_derived",
    restricted_metric_closure: bool = False,
) -> dict[str, np.ndarray | str | bool]:
    """Diagnostic positive-photon Weyl chain from Janus weak-field density source."""

    provenance = validate_lensing_factor_provenance(source_provenance)
    potential = positive_photon_lensing_potential_2d(
        positive_density_abs,
        negative_density_abs,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    components = weak_field_weyl_screen_tidal_components_2d(potential, box_size=box_size)
    return {
        **components,
        "potential": potential,
        "source_provenance": provenance,
        "restricted_metric_ready": bool(restricted_metric_closure),
        "prediction_ready": False,
    }


def shear_proxy_rms(gamma1: np.ndarray, gamma2: np.ndarray) -> float:
    """Combined RMS amplitude of two shear proxy components."""

    first = np.asarray(gamma1, dtype=float)
    second = np.asarray(gamma2, dtype=float)
    if first.shape != second.shape:
        raise ValueError("shear components must have the same shape.")
    return float(np.sqrt(np.mean(first**2 + second**2)))
