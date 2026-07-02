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
