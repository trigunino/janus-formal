from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np

from .bisector_boltzmann import (
    BiSectorParams,
    BiSectorState,
    attach_conformal_distance,
    attach_photon_baryon_history,
    attach_reionization_visibility,
    attach_visibility,
    calibrate_projection_scale_from_theta_star,
    integrate_bisector,
    integrate_photon_baryon_hierarchy,
    lensed_multipole_spectra_proxy,
    line_of_sight_multipole_spectra_proxy,
    optical_depth_profile,
    visibility_from_optical_depth,
    weyl_lensing_proxy,
)
from .z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


SOLVER_VERSION = "janus-z4-cmb-solver-stack-v1"
WEYL_LOS_NORMALIZATION = 1.0e-15


@dataclass(frozen=True)
class Z4CMBSolverSettings:
    z4_enabled: bool = True
    k: float = 0.12
    k_values: tuple[float, ...] = (0.08, 0.12, 0.25, 0.5, 0.9, 1.4, 2.5, 5.0, 10.0)
    steps: int = 384
    x_initial: float = -8.0
    x_final: float = 0.0
    ell_values: tuple[int, ...] = (2, 10, 30, 100, 300, 800, 1200, 2000)
    lensing_strength: float = 2.5e3
    opacity_norm: float = 8.0


def _hash_payload(payload: object) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _weyl_los_cl_phiphi(rows: list[dict[str, float]], ell_values: tuple[int, ...]) -> list[dict[str, float]]:
    if len(rows) < 2:
        return [{"ell": float(ell), "cl_phiphi": 0.0} for ell in ell_values]
    x = np.asarray([row["x"] for row in rows], dtype=float)
    chi = np.asarray([max(row.get("chi_conformal", 0.0), 1.0e-8) for row in rows], dtype=float)
    chi_star = float(np.max(chi))
    weyl = np.asarray([row["weyl"] for row in rows], dtype=float)
    kernel = np.maximum(chi_star - chi, 0.0) / np.maximum(chi_star * chi, 1.0e-12)
    source = kernel * weyl
    out = []
    for ell in ell_values:
        ell_factor = 4.0 / max((ell + 0.5) ** 2, 1.0)
        out.append({"ell": float(ell), "cl_phiphi": float(WEYL_LOS_NORMALIZATION * ell_factor * np.trapezoid(np.square(source), x))})
    return out


def _lens_spectra_from_phiphi(unlensed: list[dict[str, float]], cl_phiphi: list[dict[str, float]], strength: float) -> list[dict[str, float]]:
    out = []
    for row, lens in zip(unlensed, cl_phiphi):
        ell = float(row["ell"])
        smoothing = float(np.exp(-strength * max(lens["cl_phiphi"], 0.0) * ell * (ell + 1.0)))
        out.append(
            {
                **row,
                "cmb_lensing_smoothing_proxy": smoothing,
                "cl_tt_lensed_proxy": float(row["cl_tt_proxy"] * smoothing),
                "cl_te_lensed_proxy": float(row["cl_te_proxy"] * smoothing),
                "cl_ee_lensed_proxy": float(row["cl_ee_proxy"] * smoothing),
            }
        )
    return out


def params_from_cosmology(cosmology: CosmologyPoint, settings: Z4CMBSolverSettings | None = None) -> BiSectorParams:
    settings = settings or Z4CMBSolverSettings()
    h = cosmology.H0 / 100.0
    omega_plus = max((cosmology.ombh2 + cosmology.omch2) / (h * h), 1.0e-6)
    if not settings.z4_enabled:
        return BiSectorParams(
            k=settings.k,
            omega_plus=float(omega_plus),
            omega_minus=0.0,
            cross_coupling=0.0,
            projection_minus_weight=0.0,
            enforce_bianchi_closure=True,
        )
    return BiSectorParams(
        k=settings.k,
        omega_plus=float(omega_plus),
        omega_minus=0.03,
        cross_coupling=0.12,
        projection_minus_weight=0.08,
        enforce_bianchi_closure=True,
    )


def solve_z4_cmb(
    cosmology: CosmologyPoint | None = None,
    settings: Z4CMBSolverSettings | None = None,
) -> dict:
    cosmology = cosmology or CosmologyPoint()
    settings = settings or Z4CMBSolverSettings()
    if not settings.z4_enabled:
        rows = generate_camb_gr_rows(cosmology, ells=list(settings.ell_values))
        spectra = [
            {
                "ell": float(row["ell"]),
                "total": 0.0,
                "sw": 0.0,
                "doppler": 0.0,
                "isw": 0.0,
                "e_source": 0.0,
                "cl_tt_proxy": row["cl_tt"],
                "cl_te_proxy": row["cl_te"],
                "cl_ee_proxy": row["cl_ee"],
                "cmb_lensing_smoothing_proxy": 1.0,
                "cl_tt_lensed_proxy": row["cl_tt"],
                "cl_te_lensed_proxy": row["cl_te"],
                "cl_ee_lensed_proxy": row["cl_ee"],
            }
            for row in rows
        ]
        cl_phiphi = [{"ell": float(row["ell"]), "cl_phiphi": row["cl_pp"]} for row in rows]
        payload = {
            "solver_version": SOLVER_VERSION,
            "cosmology": asdict(cosmology),
            "settings": asdict(settings),
            "params": asdict(params_from_cosmology(cosmology, settings)),
            "mode_count": 0,
            "mode_weights": [],
            "background_rows": [],
            "visibility": [],
            "optical_depth": [],
            "transfer": {},
            "projection": {},
            "unlensed_spectra": spectra,
            "cl_phiphi": cl_phiphi,
            "lensed_spectra": spectra,
            "provenance": {
                "solver_version": SOLVER_VERSION,
                "cosmology_hash": _hash_payload(asdict(cosmology)),
                "settings_hash": _hash_payload(asdict(settings)),
                "theory_vector_hash": "",
                "per_cosmology_regenerated": True,
                "observed_planck_validation": False,
                "z4_enabled": False,
                "gr_limit_backend": "regenerative_camb_gr_anchor",
            },
        }
        payload["provenance"]["theory_vector_hash"] = _hash_payload(
            {
                "lensed": spectra,
                "cl_phiphi": cl_phiphi,
                "cosmology": asdict(cosmology),
                "settings": asdict(settings),
            }
        )
        return payload
    mode_outputs = []
    primary_rows = None
    primary_params = None
    primary_transfer = None
    primary_projection = None
    ns = float(cosmology.ns)
    weights = np.asarray([(k / settings.k) ** (ns - 1.0) for k in settings.k_values], dtype=float)
    weights = weights / float(np.sum(weights))
    for k, weight in zip(settings.k_values, weights):
        mode_settings = Z4CMBSolverSettings(**{**asdict(settings), "k": float(k)})
        params = params_from_cosmology(cosmology, mode_settings)
        initial = BiSectorState(
            delta_plus=1.0e-5,
            theta_plus=0.0,
            delta_minus=-2.0e-6 if settings.z4_enabled else 0.0,
            theta_minus=0.0,
        )
        rows = integrate_bisector(initial, params, x_initial=settings.x_initial, x_final=settings.x_final, steps=settings.steps)
        rows = attach_conformal_distance(rows, params)
        rows = attach_visibility(rows, params, opacity_norm=settings.opacity_norm)
        rows = attach_reionization_visibility(rows)
        rows = [{**row, "visibility": row["visibility_with_reio"]} for row in rows]
        rows = attach_photon_baryon_history(rows, k=float(k), drag=1.0)
        transfer = integrate_photon_baryon_hierarchy(rows, k=float(k), drag=1.0)
        projection = calibrate_projection_scale_from_theta_star(rows, params)
        spectra = line_of_sight_multipole_spectra_proxy(
            rows,
            transfer,
            float(k),
            ells=list(settings.ell_values),
            projection_distance_scale=projection["projection_distance_scale"],
        )
        mode_outputs.append({"k": float(k), "weight": float(weight), "rows": rows, "transfer": transfer, "projection": projection, "spectra": spectra})
        if abs(float(k) - settings.k) < 1.0e-12:
            primary_rows, primary_params, primary_transfer, primary_projection = rows, params, transfer, projection
    if primary_rows is None:
        primary = mode_outputs[0]
        primary_rows = primary["rows"]
        primary_params = params_from_cosmology(cosmology, settings)
        primary_transfer = primary["transfer"]
        primary_projection = primary["projection"]

    unlensed = []
    for index, ell in enumerate(settings.ell_values):
        row = {"ell": float(ell), "total": 0.0, "sw": 0.0, "doppler": 0.0, "isw": 0.0, "e_source": 0.0, "cl_tt_proxy": 0.0, "cl_te_proxy": 0.0, "cl_ee_proxy": 0.0}
        for mode in mode_outputs:
            source = mode["spectra"][index]
            weight = mode["weight"]
            for key in ("total", "sw", "doppler", "isw", "e_source", "cl_tt_proxy", "cl_te_proxy", "cl_ee_proxy"):
                row[key] += float(weight) * float(source[key])
        unlensed.append(row)
    cl_phiphi = _weyl_los_cl_phiphi(primary_rows, settings.ell_values)
    lensed = _lens_spectra_from_phiphi(unlensed, cl_phiphi, strength=settings.lensing_strength)
    optical_depth = optical_depth_profile(primary_rows, primary_params, opacity_norm=settings.opacity_norm)
    visibility = visibility_from_optical_depth(primary_rows, primary_params, opacity_norm=settings.opacity_norm)
    payload = {
        "solver_version": SOLVER_VERSION,
        "cosmology": asdict(cosmology),
        "settings": asdict(settings),
        "params": asdict(primary_params),
        "mode_count": len(mode_outputs),
        "mode_weights": [{"k": mode["k"], "weight": mode["weight"]} for mode in mode_outputs],
        "background_rows": primary_rows,
        "visibility": visibility,
        "optical_depth": optical_depth,
        "transfer": primary_transfer,
        "projection": primary_projection,
        "unlensed_spectra": unlensed,
        "cl_phiphi": cl_phiphi,
        "lensed_spectra": lensed,
        "provenance": {
            "solver_version": SOLVER_VERSION,
            "cosmology_hash": _hash_payload(asdict(cosmology)),
            "settings_hash": _hash_payload(asdict(settings)),
            "theory_vector_hash": "",
            "per_cosmology_regenerated": True,
            "observed_planck_validation": False,
            "z4_enabled": settings.z4_enabled,
        },
    }
    payload["provenance"]["theory_vector_hash"] = _hash_payload(
        {
            "unlensed": unlensed,
            "cl_phiphi": cl_phiphi,
            "lensed": lensed,
            "cosmology": asdict(cosmology),
            "settings": asdict(settings),
        }
    )
    return payload


def write_solver_payload(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
