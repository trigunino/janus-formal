from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

import numpy as np
from scipy.special import spherical_jn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    FIELDS,
    assemble_spectra,
    optical_window,
    primordial_power,
    solve_photon_baryon_sources,
    visibility,
)
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_source_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_source_scan.json")


def _dense_tt(rows: list[dict[str, float]]) -> tuple[np.ndarray, np.ndarray]:
    sparse_ell = np.array([row["ell"] for row in rows], dtype=float)
    ell = np.arange(int(sparse_ell[-1]) + 1, dtype=float)
    sparse_tt = np.array([row["cl_tt"] for row in rows], dtype=float)
    tt = np.interp(ell, sparse_ell, sparse_tt, left=0.0, right=sparse_tt[-1])
    tt[:2] = 0.0
    factor = ell * (ell + 1.0) / (2.0 * np.pi)
    t_cmb = 2.7255e6
    peak_mask = (ell >= 150.0) & (ell <= 320.0)
    peak = float(np.nanmax(tt[peak_mask] * factor[peak_mask] * t_cmb * t_cmb))
    scale = 5600.0 / peak if peak > 0.0 else 1.0
    return ell, tt * scale * factor * t_cmb * t_cmb


def _component_fractions(potential_horizon_scale: float, potential_time_decay: float) -> dict[str, float]:
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    pk = primordial_power(k_grid)
    sources = solve_photon_baryon_sources(
        k_grid,
        eta,
        potential_horizon_scale=potential_horizon_scale,
        potential_time_decay=potential_time_decay,
    )
    theta0, vb, psi, psi_dot, _pol_quad, _weyl = sources
    g = visibility(eta)
    e_tau = optical_window(eta)
    eta0 = 14000.0
    sw_values = []
    doppler_values = []
    isw_values = []
    interference_values = []
    for ell in range(2, 30):
        x = np.outer(k_grid, eta0 - eta)
        j = spherical_jn(ell, x)
        jp = spherical_jn(ell, x, derivative=True)
        sw_transfer = np.trapezoid(g[None, :] * (theta0 + psi) * j, eta, axis=1)
        doppler_transfer = np.trapezoid(g[None, :] * vb * jp, eta, axis=1)
        isw_transfer = np.trapezoid(e_tau[None, :] * 2.0 * psi_dot * j, eta, axis=1)
        total_transfer = sw_transfer + doppler_transfer + isw_transfer

        def cl(transfer: np.ndarray) -> float:
            return float(4.0 * math.pi * np.trapezoid(pk * transfer * transfer, np.log(k_grid)))

        sw = cl(sw_transfer)
        doppler = cl(doppler_transfer)
        isw = cl(isw_transfer)
        total = cl(total_transfer)
        component_sum = sw + doppler + isw
        if component_sum > 0.0:
            sw_values.append(sw / component_sum)
            doppler_values.append(doppler / component_sum)
            isw_values.append(isw / component_sum)
        if total > 0.0:
            interference_values.append((total - component_sum) / total)
    return {
        "sw": float(np.mean(sw_values)),
        "doppler": float(np.mean(doppler_values)),
        "isw": float(np.mean(isw_values)),
        "interference": float(np.mean(interference_values)),
    }


def score_model(potential_horizon_scale: float, potential_time_decay: float = 12000.0) -> dict:
    rows = assemble_spectra(
        potential_horizon_scale=potential_horizon_scale,
        potential_time_decay=potential_time_decay,
    )
    ell, tt = _dense_tt(rows)
    lowtt = band_score(ell, tt, "tt", 2, 29)
    peak = band_score(ell, tt, "tt", 30, 450)
    damping = band_score(ell, tt, "tt", 900, 1800)
    fractions = _component_fractions(potential_horizon_scale, potential_time_decay)
    return {
        "potential_horizon_scale": potential_horizon_scale,
        "potential_time_decay": potential_time_decay,
        "lowtt_chi2_per_dof": lowtt["chi2_per_dof"],
        "highl_tt_peak_chi2_per_dof": peak["chi2_per_dof"],
        "highl_tt_damping_chi2_per_dof": damping["chi2_per_dof"],
        "mean_component_fractions": fractions,
        "finite": all(math.isfinite(float(row[field])) for row in rows for field in FIELDS),
    }


def build_payload(scales: tuple[float, ...] = (4.0, 6.0, 8.0, 10.0, 12.0)) -> dict:
    rows = [score_model(scale) for scale in scales]
    best_lowtt = min(rows, key=lambda row: row["lowtt_chi2_per_dof"])
    active = next((row for row in rows if row["potential_horizon_scale"] == 6.0), None)
    return {
        "status": "janus-z4-scalar-source-scan",
        "native_z4_solver_used": True,
        "compressed_lcdm_parameters_used": False,
        "official_planck_likelihood_executed": False,
        "active_potential_horizon_scale": 6.0,
        "active_model_included": active is not None,
        "rows": rows,
        "best_lowtt": best_lowtt,
        "scalar_source_scan_ready": True,
        "verdict": (
            "The scan isolates whether low-l TT/SW-ISW failures are sensitive to "
            "the scalar potential decay scale. It is a shape diagnostic, not a "
            "replacement for the official Planck low-l likelihood."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar Source Scan",
        "",
        f"Status: `{payload['status']}`",
        f"Active potential horizon scale: `{payload['active_potential_horizon_scale']}`",
        f"Best lowTT scale: `{payload['best_lowtt']['potential_horizon_scale']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        fractions = row["mean_component_fractions"]
        lines.append(
            f"- scale `{row['potential_horizon_scale']}`: lowTT `{row['lowtt_chi2_per_dof']:.6g}`, "
            f"TT peak `{row['highl_tt_peak_chi2_per_dof']:.6g}`, "
            f"TT damping `{row['highl_tt_damping_chi2_per_dof']:.6g}`, "
            f"SW `{fractions['sw']:.4g}`, ISW `{fractions['isw']:.4g}`, "
            f"interference `{fractions['interference']:.4g}`"
        )
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
