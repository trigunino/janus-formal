from __future__ import annotations

import hashlib
import json
from dataclasses import asdict

import numpy as np

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint


SOURCE_LEVEL_VERSION = "janus-z4-source-level-v1"


def hash_payload(payload: object) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def source_time_grid(cosmology: CosmologyPoint, samples: int = 96) -> np.ndarray:
    start = 0.0007 * (67.4 / cosmology.H0) ** 0.15
    stop = 0.020 * (0.1200 / cosmology.omch2) ** 0.08
    return np.linspace(start, stop, samples)


def projection_ell_grid(samples: int = 96) -> np.ndarray:
    return np.linspace(2.0, 2508.0, samples)


def acoustic_window(cosmology: CosmologyPoint, ell: np.ndarray) -> np.ndarray:
    baryon_shift = 1.0 + 5.0 * (cosmology.ombh2 - 0.02237)
    matter_shift = 1.0 + 1.2 * (cosmology.omch2 - 0.1200)
    peak = 820.0 * (67.4 / cosmology.H0) ** 0.18 * matter_shift
    width = 520.0 * baryon_shift
    envelope = np.exp(-np.square((ell - peak) / width))
    envelope += 0.55 * np.exp(-np.square((ell - 215.0 * baryon_shift) / (105.0 * baryon_shift)))
    return envelope


def opacity_suppression(cosmology: CosmologyPoint, tau_grid: np.ndarray) -> np.ndarray:
    kappa = cosmology.tau * np.exp(-tau_grid / max(tau_grid[-1], 1.0e-12))
    return np.exp(-kappa)


def delta_potential_dot_sum(cosmology: CosmologyPoint, tau_grid: np.ndarray) -> np.ndarray:
    matter = cosmology.omch2 + cosmology.ombh2
    amp = (cosmology.As / 2.1e-9) * (matter / 0.14237) ** 0.35
    tilt = 1.0 + 0.6 * (cosmology.ns - 0.965)
    hubble_phase = 1.0 + 0.002 * (cosmology.H0 - 67.4)
    return amp * tilt * hubble_phase * np.sin(42.0 * tau_grid) * np.exp(-18.0 * tau_grid)


def regenerative_temperature_source_delta(cosmology: CosmologyPoint, lambda_T: float) -> dict:
    tau = source_time_grid(cosmology)
    ell = projection_ell_grid(len(tau))
    window = acoustic_window(cosmology, ell)
    opacity = opacity_suppression(cosmology, tau)
    potential = delta_potential_dot_sum(cosmology, tau)
    source = lambda_T * window * opacity * potential
    payload = {
        "version": SOURCE_LEVEL_VERSION,
        "cosmology": asdict(cosmology),
        "lambda_T": lambda_T,
        "time_grid": tau.tolist(),
        "projection_grid": ell.tolist(),
        "W_acoustic": window.tolist(),
        "exp_minus_kappa": opacity.tolist(),
        "deltaPhiDot_plus_deltaPsiDot": potential.tolist(),
        "delta_S_T_Z4": source.tolist(),
    }
    return {
        "source_payload": payload,
        "source_hash": hash_payload(payload),
        "time_grid_hash": hash_payload(payload["time_grid"]),
        "projection_grid_hash": hash_payload(payload["projection_grid"]),
        "acoustic_window_hash": hash_payload(payload["W_acoustic"]),
        "opacity_hash": hash_payload(payload["exp_minus_kappa"]),
        "potential_dot_sum_hash": hash_payload(payload["deltaPhiDot_plus_deltaPsiDot"]),
    }


def polarization_tca_switch(cosmology: CosmologyPoint, tau_grid: np.ndarray) -> np.ndarray:
    baryon_loading = cosmology.ombh2 / 0.02237
    matter_loading = (cosmology.ombh2 + cosmology.omch2) / 0.14237
    transition = 0.0068 * (67.4 / cosmology.H0) ** 0.12 * matter_loading ** 0.05
    width = 0.0022 * baryon_loading ** 0.08
    return 0.5 * (1.0 + np.tanh((tau_grid - transition) / width))


def polarization_multipoles(cosmology: CosmologyPoint, tau_grid: np.ndarray, ell_grid: np.ndarray) -> tuple[dict[str, list[float]], dict[str, list[float]]]:
    matter = cosmology.ombh2 + cosmology.omch2
    scalar_amp = (cosmology.As / 2.1e-9) * (matter / 0.14237) ** 0.22
    tilt = np.power(np.maximum(ell_grid, 2.0) / 700.0, cosmology.ns - 0.965)
    phase = 1.0 + 0.0015 * (cosmology.H0 - 67.4)
    opacity = opacity_suppression(cosmology, tau_grid)
    tca = polarization_tca_switch(cosmology, tau_grid)
    window = acoustic_window(cosmology, ell_grid)
    drive = scalar_amp * tilt * opacity * tca * window
    theta0 = drive * np.cos(35.0 * tau_grid * phase)
    theta1 = drive * np.sin(35.0 * tau_grid * phase)
    theta2 = 0.38 * drive * np.sin(17.5 * tau_grid * phase + 0.3)
    e2 = 0.24 * drive * np.cos(17.5 * tau_grid * phase - 0.2)
    e3 = 0.11 * drive * np.sin(11.5 * tau_grid * phase)
    return (
        {"Theta0": theta0.tolist(), "Theta1": theta1.tolist(), "Theta2": theta2.tolist()},
        {"E2": e2.tolist(), "E3": e3.tolist()},
    )


def regenerative_polarization_pi_source(cosmology: CosmologyPoint, lambda_E: float, hierarchy_lmax: int = 24) -> dict:
    tau = source_time_grid(cosmology)
    ell = projection_ell_grid(len(tau))
    opacity = opacity_suppression(cosmology, tau)
    tca = polarization_tca_switch(cosmology, tau)
    theta_l, e_l = polarization_multipoles(cosmology, tau, ell)
    theta2 = np.array(theta_l["Theta2"], dtype=float)
    e2 = np.array(e_l["E2"], dtype=float)
    pi_source = theta2 + e2
    delta_s_e = lambda_E * opacity * tca * pi_source
    payload = {
        "version": SOURCE_LEVEL_VERSION,
        "cosmology": asdict(cosmology),
        "lambda_E": lambda_E,
        "hierarchy_lmax": hierarchy_lmax,
        "time_grid": tau.tolist(),
        "projection_grid": ell.tolist(),
        "exp_minus_kappa": opacity.tolist(),
        "TCA_switch": tca.tolist(),
        "Theta_l": theta_l,
        "E_l": e_l,
        "Pi_source_Z4": pi_source.tolist(),
        "delta_S_E_Z4": delta_s_e.tolist(),
    }
    return {
        "source_payload": payload,
        "source_hash": hash_payload(payload),
        "time_grid_hash": hash_payload(payload["time_grid"]),
        "projection_grid_hash": hash_payload(payload["projection_grid"]),
        "opacity_grid_hash": hash_payload(payload["exp_minus_kappa"]),
        "TCA_settings_hash": hash_payload(payload["TCA_switch"]),
        "Theta_l_hash": hash_payload(payload["Theta_l"]),
        "E_l_hash": hash_payload(payload["E_l"]),
        "Pi_source_hash": hash_payload(payload["Pi_source_Z4"]),
        "hierarchy_hash": hash_payload(
            {
                "hierarchy_lmax": hierarchy_lmax,
                "Theta_l": payload["Theta_l"],
                "E_l": payload["E_l"],
                "Pi_source_Z4": payload["Pi_source_Z4"],
            }
        ),
    }
