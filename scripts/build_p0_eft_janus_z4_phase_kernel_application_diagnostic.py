from __future__ import annotations

from pathlib import Path
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    primordial_power,
    solve_photon_baryon_sources,
    transfer_for_ell,
)
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score, best_amplitude, planck_shape_reference


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_phase_kernel_application_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_phase_kernel_application_diagnostic.json")


def _tau_dot_profile(eta: np.ndarray, eta_star: float = 280.0) -> np.ndarray:
    return 2.0 * (1.0 / (1.0 + np.exp((eta - eta_star) / 22.0)) + 0.015)


def _tight_quadrupole_sources(k_grid: np.ndarray, eta: np.ndarray) -> tuple:
    theta0, vb, psi, psi_dot, _pol_quad, weyl = solve_photon_baryon_sources(k_grid, eta)
    tau_dot = _tau_dot_profile(eta)[None, :]
    k = k_grid[:, None]
    pol_quad = k * vb / np.maximum(tau_dot, 1.0e-12)
    return theta0, vb, psi, psi_dot, pol_quad, weyl


def _tight_visibility_silk_sources(k_grid: np.ndarray, eta: np.ndarray) -> tuple:
    theta0, vb, psi, psi_dot, _pol_quad, weyl = solve_photon_baryon_sources(k_grid, eta)
    tau_dot = _tau_dot_profile(eta)[None, :]
    k = k_grid[:, None]
    tight = k * vb / np.maximum(tau_dot, 1.0e-12)
    visibility_width = np.exp(-0.5 * np.square((eta - 280.0) / 18.0))[None, :]
    silk_screen = np.exp(-np.square(k / 0.13) * 0.65)
    candidate = tight * visibility_width * silk_screen
    tight_norm = float(np.sqrt(np.mean(np.square(tight)))) + 1.0e-30
    candidate_norm = float(np.sqrt(np.mean(np.square(candidate)))) + 1.0e-30
    pol_quad = candidate * (tight_norm / candidate_norm)
    return theta0, vb, psi, psi_dot, pol_quad, weyl


def _spectra_from_sources(sources: tuple, k_grid: np.ndarray, eta: np.ndarray, ell_grid: list[int]) -> dict[str, np.ndarray]:
    pk = primordial_power(k_grid)
    rows = []
    for ell in ell_grid:
        tt_t, ee_t, pp_t = transfer_for_ell(ell, k_grid, eta, sources)
        rows.append(
            {
                "ell": float(ell),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * tt_t * tt_t, np.log(k_grid))),
                "te": float(4.0 * math.pi * np.trapezoid(pk * tt_t * ee_t, np.log(k_grid))),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * ee_t * ee_t, np.log(k_grid))),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * pp_t * pp_t, np.log(k_grid))),
            }
        )
    return {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}


def _zero_crossings(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int) -> list[float]:
    mask = (ell >= ell_min) & (ell <= ell_max)
    e = ell[mask]
    v = values[mask]
    out: list[float] = []
    for idx in range(len(e) - 1):
        if v[idx] == 0.0:
            out.append(float(e[idx]))
        elif v[idx] * v[idx + 1] < 0.0:
            frac = abs(v[idx]) / (abs(v[idx]) + abs(v[idx + 1]))
            out.append(float(e[idx] + frac * (e[idx + 1] - e[idx])))
    return out


def _peak_shift(ell: np.ndarray, values: np.ndarray, channel: str, ell_min: int, ell_max: int) -> dict:
    mask = (ell >= ell_min) & (ell <= ell_max)
    e = ell[mask]
    v = values[mask]
    ref = planck_shape_reference(e, channel)
    sigma = np.maximum(np.abs(ref) * 0.18, np.nanmax(np.abs(ref)) * 0.015 + 1.0e-30)
    amp = best_amplitude(v, ref, sigma)
    scaled = amp * v
    if len(e) == 0:
        return {"model_peak_ell": None, "reference_peak_ell": None, "ell_shift": None}
    return {
        "model_peak_ell": int(e[int(np.argmax(scaled))]),
        "reference_peak_ell": int(e[int(np.argmax(ref))]),
        "ell_shift": int(e[int(np.argmax(scaled))] - e[int(np.argmax(ref))]),
    }


def _metrics(cls: dict[str, np.ndarray]) -> dict:
    ell = cls["ell"]
    return {
        "te_zero_crossings": _zero_crossings(ell, cls["te"], 30, 1200),
        "highl_te_shape": band_score(ell, cls["te"], "te", 30, 1200),
        "highl_tt_peak": _peak_shift(ell, cls["tt"], "tt", 30, 450),
        "highl_ee_shape": band_score(ell, cls["ee"], "ee", 30, 1200),
    }


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    baseline_sources = solve_photon_baryon_sources(k_grid, eta)
    tight_sources = _tight_quadrupole_sources(k_grid, eta)
    damped_sources = _tight_visibility_silk_sources(k_grid, eta)

    baseline = _spectra_from_sources(baseline_sources, k_grid, eta, ell_grid)
    tight = _spectra_from_sources(tight_sources, k_grid, eta, ell_grid)
    damped = _spectra_from_sources(damped_sources, k_grid, eta, ell_grid)
    base_metrics = _metrics(baseline)
    tight_metrics = _metrics(tight)
    damped_metrics = _metrics(damped)

    te_delta = tight_metrics["highl_te_shape"]["chi2_per_dof"] - base_metrics["highl_te_shape"]["chi2_per_dof"]
    ee_delta = tight_metrics["highl_ee_shape"]["chi2_per_dof"] - base_metrics["highl_ee_shape"]["chi2_per_dof"]
    damped_te_delta = damped_metrics["highl_te_shape"]["chi2_per_dof"] - base_metrics["highl_te_shape"]["chi2_per_dof"]
    damped_ee_delta = damped_metrics["highl_ee_shape"]["chi2_per_dof"] - base_metrics["highl_ee_shape"]["chi2_per_dof"]
    tt_shift_improved = abs(tight_metrics["highl_tt_peak"]["ell_shift"]) < abs(base_metrics["highl_tt_peak"]["ell_shift"])
    damped_tt_shift_improved = abs(damped_metrics["highl_tt_peak"]["ell_shift"]) < abs(base_metrics["highl_tt_peak"]["ell_shift"])
    te_zero_improved = len(tight_metrics["te_zero_crossings"]) > len(base_metrics["te_zero_crossings"])
    damped_te_zero_improved = len(damped_metrics["te_zero_crossings"]) > len(base_metrics["te_zero_crossings"])
    integration_recommended = bool(te_delta < 0.0 and (te_zero_improved or tt_shift_improved))
    damped_integration_recommended = bool(
        damped_te_delta < 0.0 and
        damped_ee_delta <= 0.0 and
        (damped_te_zero_improved or damped_tt_shift_improved)
    )

    return {
        "status": "janus-z4-phase-kernel-application-diagnostic",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "applied_identity": "Theta2 = k*vb/tau_dot",
        "baseline": base_metrics,
        "tight_quadrupole": tight_metrics,
        "tight_visibility_silk": damped_metrics,
        "deltas": {
            "highl_te_chi2_per_dof_delta": float(te_delta),
            "highl_ee_chi2_per_dof_delta": float(ee_delta),
            "te_zero_crossing_count_delta": int(len(tight_metrics["te_zero_crossings"]) - len(base_metrics["te_zero_crossings"])),
            "tt_peak_shift_improved": tt_shift_improved,
            "damped_highl_te_chi2_per_dof_delta": float(damped_te_delta),
            "damped_highl_ee_chi2_per_dof_delta": float(damped_ee_delta),
            "damped_te_zero_crossing_count_delta": int(len(damped_metrics["te_zero_crossings"]) - len(base_metrics["te_zero_crossings"])),
            "damped_tt_peak_shift_improved": damped_tt_shift_improved,
        },
        "integration_recommended": integration_recommended,
        "damped_integration_recommended": damped_integration_recommended,
        "safe_solver_integration_recommended": damped_integration_recommended,
        "observational_planck_gate_passed": False,
        "verdict": (
            "The tight quadrupole identity was applied in a branch-only diagnostic. "
            "Raw integration is recommended only if TE shape improves and either TE zero crossings "
            "or TT peak phase improve. Damped integration is recommended only if TE improves without "
            "worsening EE. This report does not modify the native solver."
        ),
    }


def _jsonable(payload: dict) -> dict:
    def convert(value):
        if isinstance(value, np.ndarray):
            return value.tolist()
        if isinstance(value, dict):
            return {k: convert(v) for k, v in value.items()}
        if isinstance(value, list):
            return [convert(v) for v in value]
        return value
    return convert(payload)


def write_reports() -> dict:
    payload = _jsonable(build_payload())
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Phase Kernel Application Diagnostic",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Applied identity: `{payload['applied_identity']}`",
        f"Integration recommended: `{payload['integration_recommended']}`",
        f"Damped integration recommended: `{payload['damped_integration_recommended']}`",
        f"Safe solver integration recommended: `{payload['safe_solver_integration_recommended']}`",
        "",
        "## Deltas",
    ]
    for key, value in payload["deltas"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        "## TE zero crossings",
        f"- baseline count: `{len(payload['baseline']['te_zero_crossings'])}`",
        f"- tight count: `{len(payload['tight_quadrupole']['te_zero_crossings'])}`",
        f"- tight+visibility/Silk count: `{len(payload['tight_visibility_silk']['te_zero_crossings'])}`",
        "",
        payload["verdict"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
