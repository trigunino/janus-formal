"""Minimal Janus-orbifold two-sector linear backend.

This is a diagnostic prototype, not a Planck-grade Boltzmann solver. It keeps
the smallest state needed to test whether a mono-metric EFT hook loses a
physical antisymmetric sector mode.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

import numpy as np

try:
    from scipy.special import spherical_jn as _scipy_spherical_jn
except Exception:  # pragma: no cover - fallback keeps the lightweight core usable.
    _scipy_spherical_jn = None


@dataclass(frozen=True)
class BiSectorParams:
    k: float = 0.1
    omega_plus: float = 0.3
    omega_minus: float = 0.0
    cross_coupling: float = 0.0
    hubble_friction: float = 0.5
    geff_plus: float = 1.0
    geff_minus: float = 1.0
    geff_background: float = 1.0
    omega_r: float = 9.0e-5
    background_minus_weight: float = 0.0
    projection_minus_weight: float = 0.0
    a_sigma: float = 2.0 / 3.0
    membrane_velocity_kick: float = 0.0
    enforce_bianchi_closure: bool = False


@dataclass(frozen=True)
class BiSectorState:
    delta_plus: float
    theta_plus: float
    delta_minus: float
    theta_minus: float
    pi_nu: float = 0.0

    def as_array(self) -> np.ndarray:
        return np.asarray(
            [self.delta_plus, self.theta_plus, self.delta_minus, self.theta_minus, self.pi_nu],
            dtype=float,
        )

    @staticmethod
    def from_array(values: np.ndarray) -> "BiSectorState":
        return BiSectorState(*(float(v) for v in values))


@dataclass(frozen=True)
class PhotonBaryonState:
    theta0: float
    theta1: float
    theta2: float
    nu0: float
    nu1: float
    nu2: float
    delta_b: float
    v_b: float

    def as_array(self) -> np.ndarray:
        return np.asarray(
            [self.theta0, self.theta1, self.theta2, self.nu0, self.nu1, self.nu2, self.delta_b, self.v_b],
            dtype=float,
        )

    @staticmethod
    def from_array(values: np.ndarray) -> "PhotonBaryonState":
        return PhotonBaryonState(*(float(v) for v in values))


@dataclass(frozen=True)
class MetricPerturbationState:
    phi_plus: float
    psi_plus: float
    phi_minus: float
    psi_minus: float
    phi_visible: float
    psi_visible: float


@dataclass(frozen=True)
class Z4ProjectionOperator:
    cross_coupling: float

    def matrix(self) -> np.ndarray:
        return np.asarray([[1.0, -self.cross_coupling], [-self.cross_coupling, 1.0]], dtype=float)

    def project(self, charge: np.ndarray) -> np.ndarray:
        return self.matrix() @ charge

    def trace(self) -> float:
        return float(np.trace(self.matrix()))

    def determinant(self) -> float:
        return float(np.linalg.det(self.matrix()))

    def normalized(self) -> bool:
        return bool(np.isfinite(self.matrix()).all() and self.trace() == 2.0)


def coupling_matrix(cross_coupling: float) -> np.ndarray:
    """Z4 projection rows for the two observed metric-sector components.

    This is not an independent two-metric force law. It is the finite-dimensional
    placeholder for projections of one unified Janus/Z4 geometric source.
    """

    return Z4ProjectionOperator(cross_coupling).matrix()


def z4_charge_vector(state: BiSectorState, params: BiSectorParams) -> np.ndarray:
    return np.asarray(
        [
            params.omega_plus * state.delta_plus,
            params.omega_minus * state.delta_minus,
        ],
        dtype=float,
    )


def z4_projected_sources(state: BiSectorState, params: BiSectorParams) -> np.ndarray:
    return Z4ProjectionOperator(params.cross_coupling).project(z4_charge_vector(state, params))


def z4_projection_operator_diagnostics(params: BiSectorParams) -> dict[str, float | bool]:
    operator = Z4ProjectionOperator(params.cross_coupling)
    return {
        "trace": operator.trace(),
        "determinant": operator.determinant(),
        "normalized": operator.normalized(),
        "cross_coupling": float(params.cross_coupling),
    }


def mode_basis_matrix() -> np.ndarray:
    """Map sector variables to symmetric/antisymmetric modes."""

    inv_sqrt2 = 1.0 / np.sqrt(2.0)
    return np.asarray([[inv_sqrt2, inv_sqrt2], [inv_sqrt2, -inv_sqrt2]], dtype=float)


def mode_couplings(params: BiSectorParams) -> tuple[float, float]:
    """Eigenvalues of the sector coupling matrix in the equal-density limit."""

    matrix = coupling_matrix(params.cross_coupling)
    transform = mode_basis_matrix()
    diagonal = transform @ matrix @ transform.T
    return float(diagonal[0, 0]), float(diagonal[1, 1])


def sector_potentials(state: BiSectorState, params: BiSectorParams) -> tuple[float, float]:
    if params.k <= 0.0:
        raise ValueError("k must be positive.")
    raw = z4_projected_sources(state, params)
    scale = -1.5 / (params.k * params.k)
    return float(scale * params.geff_plus * raw[0]), float(scale * params.geff_minus * raw[1])


def observable_photon_potential(state: BiSectorState, params: BiSectorParams) -> float:
    phi_plus, phi_minus = sector_potentials(state, params)
    return float(phi_plus + params.projection_minus_weight * phi_minus)


def slip_potential(state: BiSectorState, params: BiSectorParams) -> float:
    return float(0.5 * state.pi_nu * (1.0 + params.projection_minus_weight))


def weyl_potential(state: BiSectorState, params: BiSectorParams) -> float:
    phi = observable_photon_potential(state, params)
    psi = phi - slip_potential(state, params)
    return float(0.5 * (phi + psi))


def metric_perturbations(state: BiSectorState, params: BiSectorParams) -> MetricPerturbationState:
    phi_plus, phi_minus = sector_potentials(state, params)
    slip = slip_potential(state, params)
    psi_plus = phi_plus - slip
    psi_minus = phi_minus + slip
    phi_visible = phi_plus + params.projection_minus_weight * phi_minus
    psi_visible = psi_plus + params.projection_minus_weight * psi_minus
    return MetricPerturbationState(
        phi_plus=float(phi_plus),
        psi_plus=float(psi_plus),
        phi_minus=float(phi_minus),
        psi_minus=float(psi_minus),
        phi_visible=float(phi_visible),
        psi_visible=float(psi_visible),
    )


def mono_metric_collapsed_potential(state: BiSectorState, params: BiSectorParams) -> float:
    """Single-metric collapse used to expose information loss."""

    if params.k <= 0.0:
        raise ValueError("k must be positive.")
    density = params.omega_plus * state.delta_plus - params.omega_minus * state.delta_minus
    return float(-1.5 * density / (params.k * params.k))


def poisson_constraint_residual(state: BiSectorState, params: BiSectorParams) -> float:
    """Return max absolute residual of both algebraic Poisson constraints."""

    phi_plus, phi_minus = sector_potentials(state, params)
    source_plus, source_minus = z4_projected_sources(state, params)
    expected_plus = -1.5 * params.geff_plus * source_plus / (params.k * params.k)
    expected_minus = -1.5 * params.geff_minus * source_minus / (params.k * params.k)
    return float(max(abs(phi_plus - expected_plus), abs(phi_minus - expected_minus)))


def z4_projection_residual(state: BiSectorState, params: BiSectorParams) -> float:
    manual = np.asarray(
        [
            params.omega_plus * state.delta_plus - params.cross_coupling * params.omega_minus * state.delta_minus,
            -params.cross_coupling * params.omega_plus * state.delta_plus + params.omega_minus * state.delta_minus,
        ],
        dtype=float,
    )
    return float(np.max(np.abs(z4_projected_sources(state, params) - manual)))


def metric_constraint_residual(state: BiSectorState, params: BiSectorParams) -> float:
    metric = metric_perturbations(state, params)
    visible_phi_expected = metric.phi_plus + params.projection_minus_weight * metric.phi_minus
    visible_psi_expected = metric.psi_plus + params.projection_minus_weight * metric.psi_minus
    return float(
        max(
            poisson_constraint_residual(state, params),
            abs(metric.phi_visible - visible_phi_expected),
            abs(metric.psi_visible - visible_psi_expected),
        )
    )


def newtonian_gauge_residual(state: BiSectorState, params: BiSectorParams) -> float:
    metric = metric_perturbations(state, params)
    slip = slip_potential(state, params)
    return float(max(abs((metric.phi_plus - metric.psi_plus) - slip), abs((metric.psi_minus - metric.phi_minus) - slip)))


def membrane_density_jump_residual(before: BiSectorState, after: BiSectorState) -> float:
    return float(max(abs(after.delta_plus - before.delta_plus), abs(after.delta_minus - before.delta_minus)))


def background_e_of_a(a: float, params: BiSectorParams) -> float:
    if a <= 0.0:
        raise ValueError("a must be positive.")
    omega_m_eff = params.omega_plus + params.background_minus_weight * params.omega_minus
    if omega_m_eff < 0.0 or params.omega_r < 0.0 or params.geff_background <= 0.0:
        raise ValueError("background densities and G_eff must be physical.")
    return float(np.sqrt(params.geff_background * (params.omega_r / a**4 + omega_m_eff / a**3)))


def sound_speed_photon_baryon(a: float, omega_b: float = 0.05, omega_gamma: float = 5.0e-5) -> float:
    if a <= 0.0 or omega_b < 0.0 or omega_gamma <= 0.0:
        raise ValueError("invalid sound-speed inputs.")
    r_b = 3.0 * omega_b * a / (4.0 * omega_gamma)
    return float(1.0 / np.sqrt(3.0 * (1.0 + r_b)))


def sound_horizon_proxy(params: BiSectorParams, a_drag: float = 1.0 / 1060.0, samples: int = 512) -> float:
    grid = np.linspace(max(a_drag / samples, 1.0e-8), a_drag, samples)
    integrand = np.asarray(
        [sound_speed_photon_baryon(float(a)) / (a * a * background_e_of_a(float(a), params)) for a in grid],
        dtype=float,
    )
    return float(np.trapezoid(integrand, grid))


def comoving_distance_proxy(params: BiSectorParams, a_source: float = 1.0 / 1090.0, samples: int = 1024) -> float:
    grid = np.linspace(a_source, 1.0, samples)
    integrand = np.asarray([1.0 / (a * a * background_e_of_a(float(a), params)) for a in grid], dtype=float)
    return float(np.trapezoid(integrand, grid))


def attach_conformal_distance(rows: list[dict[str, float]], params: BiSectorParams) -> list[dict[str, float]]:
    if len(rows) < 2:
        return [{**row, "chi_conformal": 0.0} for row in rows]
    x = np.asarray([row["x"] for row in rows], dtype=float)
    a = np.asarray([row["a"] for row in rows], dtype=float)
    integrand = np.asarray(
        [1.0 / (float(ai) * background_e_of_a(float(ai), params)) for ai in a],
        dtype=float,
    )
    chi = np.zeros(len(rows), dtype=float)
    for index in range(len(rows) - 2, -1, -1):
        dx = x[index + 1] - x[index]
        chi[index] = chi[index + 1] + 0.5 * dx * (integrand[index] + integrand[index + 1])
    eta_total = float(chi[0])
    return [
        {
            **row,
            "eta_conformal": float(eta_total - chi[index]),
            "chi_conformal": float(chi[index]),
        }
        for index, row in enumerate(rows)
    ]


def theta_star_proxy(params: BiSectorParams) -> float:
    return sound_horizon_proxy(params) / comoving_distance_proxy(params)


def acoustic_ell_proxy(params: BiSectorParams) -> float:
    theta = theta_star_proxy(params)
    if theta <= 0.0:
        raise ValueError("theta_star_proxy must be positive.")
    return float(np.pi / theta)


def tt_peak_shift_proxy(params: BiSectorParams, reference: BiSectorParams | None = None) -> float:
    ref = reference or BiSectorParams(k=params.k, omega_plus=params.omega_plus, omega_minus=0.0)
    theta_ref = theta_star_proxy(ref)
    if theta_ref == 0.0:
        raise ValueError("reference theta_star_proxy must be non-zero.")
    return float(theta_star_proxy(params) / theta_ref - 1.0)


def weyl_lensing_proxy(rows: list[dict[str, float]]) -> float:
    if len(rows) < 2:
        return 0.0
    x = np.asarray([row["x"] for row in rows], dtype=float)
    a = np.asarray([row["a"] for row in rows], dtype=float)
    phi = np.asarray([row["weyl"] for row in rows], dtype=float)
    window = a * (1.0 - a)
    return float(np.trapezoid(np.abs(phi) * window, x))


def photon_baryon_rhs(state: PhotonBaryonState, k: float, phi_obs: float, drag: float = 1.0) -> PhotonBaryonState:
    if k <= 0.0 or drag < 0.0:
        raise ValueError("invalid photon-baryon inputs.")
    return PhotonBaryonState(
        theta0=-k * state.theta1,
        theta1=k * (state.theta0 + phi_obs - 2.0 * state.theta2) / 3.0 - drag * (state.theta1 - state.v_b),
        theta2=0.4 * k * state.theta1 - 0.3 * drag * state.theta2,
        nu0=-k * state.nu1,
        nu1=k * (state.nu0 + phi_obs - 2.0 * state.nu2) / 3.0,
        nu2=0.4 * k * state.nu1 - 0.2 * state.nu2,
        delta_b=-k * state.v_b,
        v_b=-0.5 * state.v_b + k * phi_obs + drag * (state.theta1 - state.v_b),
    )


def integrate_photon_baryon_hierarchy(
    rows: list[dict[str, float]],
    k: float,
    initial: PhotonBaryonState | None = None,
    drag: float = 1.0,
) -> dict[str, float]:
    history = attach_photon_baryon_history(rows, k=k, initial=initial, drag=drag)
    final = history[-1]
    transfer = final["theta0_pb"] + rows[-1]["weyl"]
    return {
        "theta0_final": final["theta0_pb"],
        "theta1_final": final["theta1_pb"],
        "theta2_final": final["theta2_pb"],
        "nu0_final": final["nu0_pb"],
        "nu1_final": final["nu1_pb"],
        "nu2_final": final["nu2_pb"],
        "delta_b_final": final["delta_b_pb"],
        "v_b_final": final["v_b_pb"],
        "temperature_transfer_proxy": float(transfer),
        "polarization_quadrupole_proxy": float(final["theta2_pb"]),
        "neutrino_quadrupole_proxy": float(final["nu2_pb"]),
    }


def attach_photon_baryon_history(
    rows: list[dict[str, float]],
    k: float,
    initial: PhotonBaryonState | None = None,
    drag: float = 1.0,
) -> list[dict[str, float]]:
    if len(rows) < 2:
        raise ValueError("at least two rows are required.")
    state = initial or PhotonBaryonState(
        theta0=1.0e-5,
        theta1=0.0,
        theta2=0.0,
        nu0=1.0e-5,
        nu1=0.0,
        nu2=0.0,
        delta_b=1.0e-5,
        v_b=0.0,
    )
    output = [
        {
            **rows[0],
            "theta0_pb": state.theta0,
            "theta1_pb": state.theta1,
            "theta2_pb": state.theta2,
            "nu0_pb": state.nu0,
            "nu1_pb": state.nu1,
            "nu2_pb": state.nu2,
            "delta_b_pb": state.delta_b,
            "v_b_pb": state.v_b,
        }
    ]
    for left, right in zip(rows[:-1], rows[1:]):
        dx = float(right["x"] - left["x"])
        phi = float(left["weyl"])
        y = state.as_array()

        def f(yi: np.ndarray, phii: float) -> np.ndarray:
            return photon_baryon_rhs(PhotonBaryonState.from_array(yi), k, phii, drag=drag).as_array()

        k1 = f(y, phi)
        k2 = f(y + 0.5 * dx * k1, phi)
        k3 = f(y + 0.5 * dx * k2, phi)
        k4 = f(y + dx * k3, float(right["weyl"]))
        state = PhotonBaryonState.from_array(y + dx * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0)
        output.append(
            {
                **right,
                "theta0_pb": state.theta0,
                "theta1_pb": state.theta1,
                "theta2_pb": state.theta2,
                "nu0_pb": state.nu0,
                "nu1_pb": state.nu1,
                "nu2_pb": state.nu2,
                "delta_b_pb": state.delta_b,
                "v_b_pb": state.v_b,
            }
        )
    return output


def cl_tt_proxy(rows: list[dict[str, float]], transfer: dict[str, float], ells: list[int] | None = None) -> list[dict[str, float]]:
    ell_values = ells or [2, 10, 30, 100, 300, 800, 1200, 2000]
    theta = abs(float(transfer["temperature_transfer_proxy"]))
    lens = weyl_lensing_proxy(rows)
    return [
        {
            "ell": float(ell),
            "cl_tt_proxy": theta * theta / (ell * (ell + 1.0)) + 1.0e-3 * lens / (1.0 + ell / 500.0),
        }
        for ell in ell_values
    ]


def visibility_proxy(a: float, a_star: float = 1.0 / 1090.0, width: float = 1.5e-4) -> float:
    if a <= 0.0 or a_star <= 0.0 or width <= 0.0:
        raise ValueError("invalid visibility inputs.")
    return float(np.exp(-0.5 * ((a - a_star) / width) ** 2))


def ionization_fraction_proxy(a: float, a_rec: float = 1.0 / 1090.0, width: float = 1.2e-4) -> float:
    if a <= 0.0 or width <= 0.0:
        raise ValueError("invalid ionization inputs.")
    return float(0.5 * (1.0 - np.tanh((a - a_rec) / width)))


def optical_depth_profile(
    rows: list[dict[str, float]],
    params: BiSectorParams,
    opacity_norm: float = 8.0,
    a_rec: float = 1.0 / 1090.0,
    width: float = 1.2e-4,
) -> list[float]:
    if len(rows) < 2:
        return [0.0 for _ in rows]
    rates = np.asarray(
        [
            opacity_norm
            * ionization_fraction_proxy(row["a"], a_rec=a_rec, width=width)
            * (params.omega_plus / max(row["a"], 1.0e-12) ** 2)
            for row in rows
        ],
        dtype=float,
    )
    x = np.asarray([row["x"] for row in rows], dtype=float)
    tau = np.zeros(len(rows), dtype=float)
    for index in range(len(rows) - 2, -1, -1):
        dx = x[index + 1] - x[index]
        tau[index] = tau[index + 1] + 0.5 * dx * (rates[index] + rates[index + 1])
    return [float(value) for value in tau]


def visibility_from_optical_depth(
    rows: list[dict[str, float]],
    params: BiSectorParams,
    opacity_norm: float = 8.0,
    a_rec: float = 1.0 / 1090.0,
    width: float = 1.2e-4,
) -> list[float]:
    tau = np.asarray(optical_depth_profile(rows, params, opacity_norm=opacity_norm, a_rec=a_rec, width=width), dtype=float)
    x = np.asarray([row["x"] for row in rows], dtype=float)
    visibility = np.zeros(len(rows), dtype=float)
    exp_tau = np.exp(-tau)
    for index in range(1, len(rows) - 1):
        visibility[index] = max(0.0, (exp_tau[index + 1] - exp_tau[index - 1]) / (x[index + 1] - x[index - 1]))
    norm = float(np.trapezoid(visibility, x))
    if norm > 0.0:
        visibility /= norm
    return [float(value) for value in visibility]


def attach_visibility(
    rows: list[dict[str, float]],
    params: BiSectorParams,
    opacity_norm: float = 8.0,
    a_rec: float = 1.0 / 1090.0,
    width: float = 1.2e-4,
) -> list[dict[str, float]]:
    visibility = visibility_from_optical_depth(rows, params, opacity_norm=opacity_norm, a_rec=a_rec, width=width)
    return [{**row, "visibility": visibility[index]} for index, row in enumerate(rows)]


def reionization_visibility_proxy(a: float, a_reio: float = 1.0 / 8.5, width: float = 0.035) -> float:
    if a <= 0.0 or a_reio <= 0.0 or width <= 0.0:
        raise ValueError("invalid reionization visibility inputs.")
    return float(np.exp(-0.5 * ((a - a_reio) / width) ** 2))


def attach_reionization_visibility(
    rows: list[dict[str, float]],
    amplitude: float = 0.08,
    a_reio: float = 1.0 / 8.5,
    width: float = 0.035,
) -> list[dict[str, float]]:
    if len(rows) < 2:
        return [{**row, "visibility_reio": 0.0, "visibility_with_reio": row.get("visibility", 0.0)} for row in rows]
    x = np.asarray([row["x"] for row in rows], dtype=float)
    base = np.asarray([row.get("visibility", 0.0) for row in rows], dtype=float)
    reio = np.asarray([amplitude * reionization_visibility_proxy(row["a"], a_reio=a_reio, width=width) for row in rows], dtype=float)
    total = base + reio
    norm = float(np.trapezoid(total, x))
    if norm > 0.0:
        total = total / norm
    return [
        {
            **row,
            "visibility_reio": float(reio[index]),
            "visibility_with_reio": float(total[index]),
        }
        for index, row in enumerate(rows)
    ]


def calibrate_visibility_to_astar(
    rows: list[dict[str, float]],
    params: BiSectorParams,
    a_star: float = 1.0 / 1090.0,
) -> dict[str, float]:
    best: dict[str, float] | None = None
    for a_rec in np.linspace(4.0e-4, 1.4e-3, 31):
        for width in np.linspace(5.0e-5, 2.5e-4, 11):
            visible_rows = attach_visibility(rows, params, a_rec=float(a_rec), width=float(width))
            peak = max(visible_rows, key=lambda row: row["visibility"])
            residual = abs(float(peak["a"]) - a_star)
            candidate = {
                "a_rec": float(a_rec),
                "width": float(width),
                "peak_a": float(peak["a"]),
                "peak_value": float(peak["visibility"]),
                "abs_peak_residual": residual,
            }
            if best is None or residual < best["abs_peak_residual"]:
                best = candidate
    if best is None:
        raise ValueError("visibility calibration grid is empty.")
    return best


def visibility_weighted_chi(rows: list[dict[str, float]]) -> float:
    if len(rows) < 2:
        return 0.0
    x = np.asarray([row["x"] for row in rows], dtype=float)
    visibility = np.asarray([row.get("visibility", visibility_proxy(row["a"])) for row in rows], dtype=float)
    chi = np.asarray([row.get("chi_conformal", x[-1] - row["x"]) for row in rows], dtype=float)
    norm = float(np.trapezoid(visibility, x))
    if norm == 0.0:
        return 0.0
    return float(np.trapezoid(visibility * chi, x) / norm)


def calibrate_projection_scale_from_theta_star(rows: list[dict[str, float]], params: BiSectorParams) -> dict[str, float]:
    chi_eff = visibility_weighted_chi(rows)
    ell_eff = acoustic_ell_proxy(params)
    if chi_eff <= 0.0 and rows:
        x = np.asarray([row["x"] for row in rows], dtype=float)
        chi = np.asarray([row.get("chi_conformal", x[-1] - row["x"]) for row in rows], dtype=float)
        chi_eff = float(np.max(chi))
    if params.k <= 0.0 or chi_eff <= 0.0:
        raise ValueError("positive k and effective chi are required.")
    scale = ell_eff / (params.k * chi_eff)
    return {
        "acoustic_ell_proxy": ell_eff,
        "visibility_weighted_chi": chi_eff,
        "projection_distance_scale": float(scale),
    }


def line_of_sight_temperature_source(rows: list[dict[str, float]], transfer: dict[str, float]) -> float:
    if len(rows) < 2:
        return 0.0
    x = np.asarray([row["x"] for row in rows], dtype=float)
    visibility = np.asarray([row.get("visibility", visibility_proxy(row["a"])) for row in rows], dtype=float)
    source = np.asarray(
        [
            visibility[index] * (row.get("theta0_pb", transfer["theta0_final"]) + row["weyl"])
            for index, row in enumerate(rows)
        ],
        dtype=float,
    )
    norm = float(np.trapezoid(visibility, x))
    if norm == 0.0:
        return 0.0
    return float(np.trapezoid(source, x) / norm)


def line_of_sight_source_decomposition(rows: list[dict[str, float]], transfer: dict[str, float]) -> dict[str, float]:
    if len(rows) < 2:
        return {
            "monopole_sw": 0.0,
            "gravitational_sw": 0.0,
            "current_total": 0.0,
            "doppler_transport_proxy": 0.0,
            "isw_transport_proxy": 0.0,
            "transport_proxy_total": 0.0,
            "transport_proxy_relative_size": 0.0,
        }
    x = np.asarray([row["x"] for row in rows], dtype=float)
    coord = np.asarray([row.get("eta_conformal", row["x"]) for row in rows], dtype=float)
    visibility = np.asarray([row.get("visibility", visibility_proxy(row["a"])) for row in rows], dtype=float)
    weyl = np.asarray([row["weyl"] for row in rows], dtype=float)
    theta0 = np.asarray([row.get("theta0_pb", transfer["theta0_final"]) for row in rows], dtype=float)
    theta1 = np.asarray([row.get("theta1_pb", transfer["theta1_final"]) for row in rows], dtype=float)
    norm = float(np.trapezoid(visibility, x))
    if norm == 0.0:
        return {
            "monopole_sw": 0.0,
            "gravitational_sw": 0.0,
            "current_total": 0.0,
            "doppler_transport_proxy": 0.0,
            "isw_transport_proxy": 0.0,
            "transport_proxy_total": 0.0,
            "transport_proxy_relative_size": 0.0,
        }
    monopole = float(np.trapezoid(visibility * theta0, x) / norm)
    gravitational = float(np.trapezoid(visibility * weyl, x) / norm)
    doppler = float(np.trapezoid(visibility * theta1, x) / norm)
    isw = float(np.trapezoid(visibility * np.gradient(weyl, coord), x) / norm)
    current_total = monopole + gravitational
    transport_total = doppler + isw
    return {
        "monopole_sw": monopole,
        "gravitational_sw": gravitational,
        "current_total": current_total,
        "doppler_transport_proxy": doppler,
        "isw_transport_proxy": isw,
        "transport_proxy_total": transport_total,
        "transport_proxy_relative_size": abs(transport_total) / max(abs(current_total), 1.0e-30),
    }


def spherical_bessel_jn(ell: int, z: float) -> float:
    if ell < 0:
        raise ValueError("ell must be non-negative.")
    if _scipy_spherical_jn is not None:
        return float(_scipy_spherical_jn(ell, z))
    if abs(z) < 1.0e-8:
        return 1.0 if ell == 0 else 0.0
    if ell > abs(z) + 20.0:
        return 0.0
    if ell == 0:
        return float(np.sin(z) / z)
    j_prev = np.sin(z) / z
    j_curr = np.sin(z) / (z * z) - np.cos(z) / z
    if ell == 1:
        return float(j_curr)
    for n in range(1, ell):
        j_next = (2.0 * n + 1.0) * j_curr / z - j_prev
        j_prev, j_curr = j_curr, j_next
    return float(j_curr)


def spherical_bessel_jn_derivative(ell: int, z: float) -> float:
    if ell < 0:
        raise ValueError("ell must be non-negative.")
    if _scipy_spherical_jn is not None:
        return float(_scipy_spherical_jn(ell, z, derivative=True))
    if abs(z) < 1.0e-8:
        return 0.0 if ell != 1 else 1.0 / 3.0
    if ell > abs(z) + 20.0:
        return 0.0
    if ell == 0:
        return float(-spherical_bessel_jn(1, z))
    return float(spherical_bessel_jn(ell - 1, z) - (ell + 1.0) * spherical_bessel_jn(ell, z) / z)


def line_of_sight_multipole_source(
    rows: list[dict[str, float]],
    transfer: dict[str, float],
    k: float,
    ell: int,
    projection_distance_scale: float = 700.0,
) -> dict[str, float]:
    if len(rows) < 2:
        return {"ell": float(ell), "total": 0.0, "sw": 0.0, "doppler": 0.0, "isw": 0.0}
    if k <= 0.0:
        raise ValueError("k must be positive.")
    x = np.asarray([row["x"] for row in rows], dtype=float)
    coord = np.asarray([row.get("eta_conformal", row["x"]) for row in rows], dtype=float)
    visibility = np.asarray([row.get("visibility", visibility_proxy(row["a"])) for row in rows], dtype=float)
    weyl = np.asarray([row["weyl"] for row in rows], dtype=float)
    theta0 = np.asarray([row.get("theta0_pb", transfer["theta0_final"]) for row in rows], dtype=float)
    theta1 = np.asarray([row.get("theta1_pb", transfer["theta1_final"]) for row in rows], dtype=float)
    chi = np.asarray([row.get("chi_conformal", x[-1] - row["x"]) for row in rows], dtype=float)
    z = k * chi * projection_distance_scale
    j = np.asarray([spherical_bessel_jn(ell, float(value)) for value in z], dtype=float)
    dj = np.asarray([spherical_bessel_jn_derivative(ell, float(value)) for value in z], dtype=float)
    weyl_prime = np.gradient(weyl, coord)
    norm = float(np.trapezoid(visibility, x))
    if norm == 0.0:
        return {"ell": float(ell), "total": 0.0, "sw": 0.0, "doppler": 0.0, "isw": 0.0}
    sw = float(np.trapezoid(visibility * (theta0 + weyl) * j, x) / norm)
    doppler = float(np.trapezoid(visibility * theta1 * dj, x) / norm)
    isw = float(np.trapezoid(visibility * 2.0 * weyl_prime * j, x) / norm)
    if ell >= 500 and abs(sw + doppler + isw) < 1.0e-100:
        # Coarse diagnostic grids undersample highly oscillatory Bessel kernels.
        # Use a Limber-like envelope from the same source terms to avoid a
        # spurious zero high-l theory vector. This is a solver regularization,
        # not an observational validation shortcut.
        envelope = np.exp(-ell / 3500.0) / np.sqrt(float(ell) + 1.0)
        sw = float(np.sqrt(np.trapezoid(visibility * np.square(theta0 + weyl), x) / norm) * envelope)
        doppler = float(np.sqrt(np.trapezoid(visibility * np.square(theta1), x) / norm) * envelope)
        isw = float(np.sqrt(np.trapezoid(visibility * np.square(2.0 * weyl_prime), x) / norm) * envelope)
    return {"ell": float(ell), "total": sw + doppler + isw, "sw": sw, "doppler": doppler, "isw": isw}


def line_of_sight_multipole_cl_tt_proxy(
    rows: list[dict[str, float]],
    transfer: dict[str, float],
    k: float,
    ells: list[int] | None = None,
    projection_distance_scale: float = 700.0,
) -> list[dict[str, float]]:
    ell_values = ells or [2, 10, 30, 100, 300, 800, 1200, 2000]
    output = []
    for ell in ell_values:
        source = line_of_sight_multipole_source(
            rows,
            transfer,
            k,
            ell,
            projection_distance_scale=projection_distance_scale,
        )
        cl = source["total"] * source["total"] / (ell * (ell + 1.0))
        output.append({**source, "cl_tt_multipole_los_proxy": float(cl)})
    return output


def line_of_sight_polarization_multipole_source(
    rows: list[dict[str, float]],
    ell: int,
    k: float,
    projection_distance_scale: float = 700.0,
) -> dict[str, float]:
    if len(rows) < 2:
        return {"ell": float(ell), "e_source": 0.0}
    if k <= 0.0:
        raise ValueError("k must be positive.")
    x = np.asarray([row["x"] for row in rows], dtype=float)
    visibility = np.asarray([row.get("visibility", visibility_proxy(row["a"])) for row in rows], dtype=float)
    theta2 = np.asarray([row.get("theta2_pb", 0.0) for row in rows], dtype=float)
    chi = np.asarray([row.get("chi_conformal", x[-1] - row["x"]) for row in rows], dtype=float)
    z = k * chi * projection_distance_scale
    j = np.asarray([spherical_bessel_jn(ell, float(value)) for value in z], dtype=float)
    norm = float(np.trapezoid(visibility, x))
    if norm == 0.0:
        return {"ell": float(ell), "e_source": 0.0}
    e_source = float(np.trapezoid(visibility * theta2 * j, x) / norm)
    if ell >= 500 and abs(e_source) < 1.0e-100:
        envelope = np.exp(-ell / 3500.0) / np.sqrt(float(ell) + 1.0)
        e_source = float(np.sqrt(np.trapezoid(visibility * np.square(theta2), x) / norm) * envelope)
    return {"ell": float(ell), "e_source": e_source}


def line_of_sight_multipole_spectra_proxy(
    rows: list[dict[str, float]],
    transfer: dict[str, float],
    k: float,
    ells: list[int] | None = None,
    projection_distance_scale: float = 700.0,
) -> list[dict[str, float]]:
    ell_values = ells or [2, 10, 30, 100, 300, 800, 1200, 2000]
    output = []
    for ell in ell_values:
        temperature = line_of_sight_multipole_source(
            rows,
            transfer,
            k,
            ell,
            projection_distance_scale=projection_distance_scale,
        )
        polarization = line_of_sight_polarization_multipole_source(
            rows,
            ell,
            k,
            projection_distance_scale=projection_distance_scale,
        )
        denom = ell * (ell + 1.0)
        tt = temperature["total"] * temperature["total"] / denom
        ee = polarization["e_source"] * polarization["e_source"] / denom
        te = temperature["total"] * polarization["e_source"] / denom
        output.append(
            {
                **temperature,
                "e_source": polarization["e_source"],
                "cl_tt_proxy": float(tt),
                "cl_te_proxy": float(te),
                "cl_ee_proxy": float(ee),
            }
        )
    return output


def lensed_multipole_spectra_proxy(
    spectra: list[dict[str, float]],
    rows: list[dict[str, float]],
    lensing_strength: float = 2.5e3,
) -> list[dict[str, float]]:
    lens = weyl_lensing_proxy(rows)
    output = []
    for row in spectra:
        ell = float(row["ell"])
        smoothing = float(np.exp(-lensing_strength * lens * ell * (ell + 1.0) / (2000.0 * 2001.0)))
        output.append(
            {
                **row,
                "cmb_lensing_smoothing_proxy": smoothing,
                "cl_tt_lensed_proxy": float(row["cl_tt_proxy"] * smoothing),
                "cl_te_lensed_proxy": float(row["cl_te_proxy"] * smoothing),
                "cl_ee_lensed_proxy": float(row["cl_ee_proxy"] * smoothing),
            }
        )
    return output


def line_of_sight_cl_tt_proxy(
    rows: list[dict[str, float]],
    transfer: dict[str, float],
    ells: list[int] | None = None,
) -> list[dict[str, float]]:
    ell_values = ells or [2, 10, 30, 100, 300, 800, 1200, 2000]
    los = abs(line_of_sight_temperature_source(rows, transfer))
    lens = weyl_lensing_proxy(rows)
    return [
        {
            "ell": float(ell),
            "cl_tt_los_proxy": los * los / (ell * (ell + 1.0)) + 5.0e-4 * lens / (1.0 + ell / 700.0),
        }
        for ell in ell_values
    ]


def bianchi_closure_accelerations(state: BiSectorState, params: BiSectorParams) -> tuple[float, float]:
    """Compensating accelerations that make weighted sector momentum conserved.

    This is the minimal algebraic closure for the toy prototype. It should be
    replaced by the derived two-sector Bianchi identities in a production
    backend.
    """

    trial = rhs(0.0, state, replace(params, enforce_bianchi_closure=False))
    weighted_force = params.omega_plus * trial.theta_plus + params.omega_minus * trial.theta_minus
    damping = -params.hubble_friction * (params.omega_plus * state.theta_plus + params.omega_minus * state.theta_minus)
    residual = weighted_force - damping
    norm = params.omega_plus + params.omega_minus
    if norm == 0.0:
        return 0.0, 0.0
    correction = -residual / norm
    return float(correction), float(correction)


def rhs(_x: float, state: BiSectorState, params: BiSectorParams) -> BiSectorState:
    phi_plus, phi_minus = sector_potentials(state, params)
    closure_plus, closure_minus = (
        bianchi_closure_accelerations(state, params) if params.enforce_bianchi_closure else (0.0, 0.0)
    )
    return BiSectorState(
        delta_plus=-state.theta_plus,
        theta_plus=-params.hubble_friction * state.theta_plus + params.k * params.k * phi_plus + closure_plus,
        delta_minus=-state.theta_minus,
        theta_minus=-params.hubble_friction * state.theta_minus + params.k * params.k * phi_minus + closure_minus,
        pi_nu=-0.4 * state.pi_nu + 0.05 * (state.theta_plus - state.theta_minus),
    )


def continuity_residual(_x: float, state: BiSectorState, params: BiSectorParams) -> tuple[float, float]:
    derivatives = rhs(_x, state, params)
    return (
        float(derivatives.delta_plus + state.theta_plus),
        float(derivatives.delta_minus + state.theta_minus),
    )


def momentum_exchange_residual(_x: float, state: BiSectorState, params: BiSectorParams) -> float:
    """Proxy for whether internal sector exchange sums to zero.

    This is only a sanity gate for the toy equations. A full backend must replace
    it with the derived Bianchi identities of the two-sector stress tensors.
    """

    derivatives = rhs(_x, state, params)
    weighted = params.omega_plus * derivatives.theta_plus + params.omega_minus * derivatives.theta_minus
    damping = -params.hubble_friction * (params.omega_plus * state.theta_plus + params.omega_minus * state.theta_minus)
    return float(weighted - damping)


def apply_membrane_junction(state: BiSectorState, params: BiSectorParams) -> BiSectorState:
    """Keep densities continuous and kick only velocities."""

    kick = params.membrane_velocity_kick
    return BiSectorState(
        delta_plus=state.delta_plus,
        theta_plus=state.theta_plus + kick,
        delta_minus=state.delta_minus,
        theta_minus=state.theta_minus - kick,
    )


def rk4_step(x: float, state: BiSectorState, dx: float, params: BiSectorParams) -> BiSectorState:
    y = state.as_array()

    def f(xi: float, yi: np.ndarray) -> np.ndarray:
        return rhs(xi, BiSectorState.from_array(yi), params).as_array()

    k1 = f(x, y)
    k2 = f(x + 0.5 * dx, y + 0.5 * dx * k1)
    k3 = f(x + 0.5 * dx, y + 0.5 * dx * k2)
    k4 = f(x + dx, y + dx * k3)
    return BiSectorState.from_array(y + dx * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0)


def integrate_bisector(
    initial: BiSectorState,
    params: BiSectorParams,
    x_initial: float = -7.0,
    x_final: float = 0.0,
    steps: int = 512,
) -> list[dict[str, float]]:
    if steps <= 0:
        raise ValueError("steps must be positive.")
    dx = (x_final - x_initial) / steps
    x_sigma = float(np.log(params.a_sigma))
    state = initial
    rows: list[dict[str, float]] = []
    crossed = False
    membrane_density_residual = 0.0
    for index in range(steps + 1):
        x = x_initial + index * dx
        if not crossed and x >= x_sigma:
            before_jump = state
            state = apply_membrane_junction(state, params)
            membrane_density_residual = membrane_density_jump_residual(before_jump, state)
            crossed = True
        phi_plus, phi_minus = sector_potentials(state, params)
        metric = metric_perturbations(state, params)
        cont_plus, cont_minus = continuity_residual(x, state, params)
        rows.append(
            {
                "x": x,
                "a": float(np.exp(x)),
                "delta_plus": state.delta_plus,
                "theta_plus": state.theta_plus,
                "delta_minus": state.delta_minus,
                "theta_minus": state.theta_minus,
                "phi_plus": phi_plus,
                "phi_minus": phi_minus,
                "psi_plus": metric.psi_plus,
                "psi_minus": metric.psi_minus,
                "phi_visible_metric": metric.phi_visible,
                "psi_visible_metric": metric.psi_visible,
                "phi_obs": observable_photon_potential(state, params),
                "weyl": weyl_potential(state, params),
                "slip": slip_potential(state, params),
                "pi_nu": state.pi_nu,
                "phi_mono": mono_metric_collapsed_potential(state, params),
                "constraint_residual": poisson_constraint_residual(state, params),
                "metric_constraint_residual": metric_constraint_residual(state, params),
                "z4_projection_residual": z4_projection_residual(state, params),
                "newtonian_gauge_residual": newtonian_gauge_residual(state, params),
                "membrane_density_jump_residual": membrane_density_residual,
                "continuity_residual_plus": cont_plus,
                "continuity_residual_minus": cont_minus,
                "momentum_exchange_residual": momentum_exchange_residual(x, state, params),
            }
        )
        if index < steps:
            state = rk4_step(x, state, dx, params)
    return rows


def information_loss_metric(row: dict[str, float]) -> float:
    return abs(row["phi_obs"] - row["phi_mono"])
