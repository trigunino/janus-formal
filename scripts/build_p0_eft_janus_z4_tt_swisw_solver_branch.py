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

from scripts.build_p0_eft_janus_negative_sector_cmb_imprint import _imprint_weight
from scripts.build_p0_eft_janus_z4_controlled_geometric_solver_branch import _geometric_sources, _shape_summary
from scripts.build_p0_eft_janus_z4_integrated_negative_imprint_branch import _assemble_integrated
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    optical_window,
    primordial_power,
    transfer_for_ell,
    visibility,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_solver_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_solver_branch.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_solver_branch_spectra.csv")
FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]


def _reflect_time(arr: np.ndarray) -> np.ndarray:
    return arr[:, ::-1]


def _hidden_acoustic_response(
    k_grid: np.ndarray,
    eta: np.ndarray,
    psi_plus: np.ndarray,
    projection_b: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    psi_minus = _reflect_time(psi_plus)
    phi_minus = psi_minus
    phi_minus_dot = np.gradient(phi_minus, eta, axis=1)
    phi_minus_dd = np.gradient(phi_minus_dot, eta, axis=1)
    eta_star = 280.0
    r_baryon = 0.62 * np.minimum(eta / eta_star, 1.0)
    cs2 = 1.0 / (3.0 * (1.0 + r_baryon))
    k2 = np.square(k_grid)[:, None]
    source = -projection_b * (phi_minus_dd + cs2[None, :] * k2 * psi_minus)
    delta_theta = np.zeros_like(psi_plus)
    delta_theta_dot = np.zeros_like(psi_plus)
    max_k = float(np.max(k_grid))
    for idx in range(len(eta) - 1):
        dt_total = float(eta[idx + 1] - eta[idx])
        substeps = max(1, int(math.ceil(dt_total * max_k * math.sqrt(float(cs2[idx])) / 0.18)))
        dt = dt_total / substeps
        omega2 = cs2[idx] * np.square(k_grid)
        th = delta_theta[:, idx].copy()
        vel = delta_theta_dot[:, idx].copy()
        src = source[:, idx]
        for _ in range(substeps):
            acc = src - omega2 * th
            vel_half = vel + 0.5 * dt * acc
            th = th + dt * vel_half
            acc_new = src - omega2 * th
            vel = vel_half + 0.5 * dt * acc_new
        delta_theta[:, idx + 1] = np.nan_to_num(th, nan=0.0, posinf=0.0, neginf=0.0)
        delta_theta_dot[:, idx + 1] = np.nan_to_num(vel, nan=0.0, posinf=0.0, neginf=0.0)
    delta_v = -3.0 * (delta_theta_dot + projection_b * phi_minus_dot) / np.maximum(k_grid[:, None], 1.0e-8)
    return delta_theta, delta_v, psi_minus, phi_minus_dot


def _transfer_for_ell_ttswisw(
    ell: int,
    k_grid: np.ndarray,
    eta: np.ndarray,
    sources: tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray],
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    eta0 = 14000.0
    theta0, vb, psi, psi_dot, pol_quad, weyl = sources
    delta_theta, delta_v, psi_minus, phi_minus_dot = _hidden_acoustic_response(k_grid, eta, psi)
    low_l_window = 1.0 / (1.0 + (max(float(ell), 1.0) / 30.0) ** 4)

    g = visibility(eta)
    e_tau = optical_window(eta)
    x = np.outer(k_grid, eta0 - eta)
    j = spherical_jn(ell, x)
    jp = spherical_jn(ell, x, derivative=True)
    spin2_norm = math.sqrt(float((ell + 2) * (ell + 1) * max(ell, 1) * max(ell - 1, 0))) if ell >= 2 else 0.0
    e_kernel = spin2_norm * j / np.square(np.maximum(x, 1.0e-6))

    chi_star = eta0 - 280.0
    chi = np.maximum(eta0 - eta, 1.0)
    lens_kernel = np.where(eta > 280.0, 2.0 * (eta - 280.0) / (chi_star * chi), 0.0)

    visible = (
        g[None, :] * (theta0 + psi) * j
        + g[None, :] * vb * jp
        + e_tau[None, :] * 2.0 * psi_dot * j
    )
    hidden = (
        g[None, :] * (delta_theta + psi_minus) * j
        + g[None, :] * delta_v * jp
        + e_tau[None, :] * 2.0 * phi_minus_dot * j
    )
    tt = np.trapezoid(visible + (1.0 - low_l_window) * hidden, eta, axis=1)
    ee = np.trapezoid(g[None, :] * pol_quad * e_kernel, eta, axis=1)
    pp = np.trapezoid(lens_kernel[None, :] * weyl * j, eta, axis=1)
    return tt, ee, pp


def _assemble_branch(ell_grid: list[int], k_grid: np.ndarray, eta: np.ndarray) -> dict[str, np.ndarray]:
    sources = _geometric_sources(k_grid, eta)
    pk = primordial_power(k_grid) * _imprint_weight(k_grid, "jeans_blue")
    log_k = np.log(k_grid)
    rows = []
    for ell in ell_grid:
        tt_t, ee_t, pp_t = _transfer_for_ell_ttswisw(ell, k_grid, eta, sources)
        rows.append(
            {
                "ell": float(ell),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * tt_t * tt_t, log_k)),
                "te": float(4.0 * math.pi * np.trapezoid(pk * tt_t * ee_t, log_k)),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * ee_t * ee_t, log_k)),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * pp_t * pp_t, log_k)),
            }
        )
    return {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}


def _delta_summary(branch: dict, baseline: dict) -> dict:
    return {
        key: float(branch[key]["chi2_per_dof"] - baseline[key]["chi2_per_dof"])
        for key in ["lowTT", "highl_TT_peak1", "highl_TE", "highl_EE", "lensing"]
    }


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + list(range(1202, 2509, 40)) + [2508]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    integrated_cls = _assemble_integrated(ell_grid, k_grid, eta)
    branch_cls = _assemble_branch(ell_grid, k_grid, eta)
    integrated_shape = _shape_summary(integrated_cls)
    branch_shape = _shape_summary(branch_cls)
    deltas = _delta_summary(branch_shape, integrated_shape)

    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        for idx, ell in enumerate(branch_cls["ell"]):
            writer.writerow(
                {
                    "ell": int(ell),
                    "cl_tt": branch_cls["tt"][idx],
                    "cl_te": branch_cls["te"][idx],
                    "cl_ee": branch_cls["ee"][idx],
                    "cl_pp": branch_cls["pp"][idx],
                }
            )
    finite = all(np.isfinite(branch_cls[key]).all() for key in ["tt", "te", "ee", "pp"])
    safe_for_gate = bool(
        finite and
        deltas["lowTT"] <= 0.0 and
        deltas["highl_TT_peak1"] <= 0.0 and
        deltas["highl_TE"] <= 2.0 and
        deltas["highl_EE"] <= 1.0
    )
    return {
        "status": "janus-z4-tt-swisw-solver-branch",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "mechanisms": [
            "derived projected TT acoustic source",
            "hidden-sector SW/ISW cancellation in low-l window",
            "controlled geometric branch",
            "fixed jeans_blue negative-sector primordial imprint",
        ],
        "spectra_path": str(SPECTRA_PATH),
        "finite_spectra_exported": bool(finite),
        "integrated_shape": integrated_shape,
        "branch_shape": branch_shape,
        "deltas_vs_integrated_negative_imprint_branch": deltas,
        "safe_for_official_gate": safe_for_gate,
        "observational_planck_gate_passed": False,
        "next": "Run a dedicated Planck gate only if safe_for_official_gate is true.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 TT/SW-ISW Solver Branch",
        "",
        f"Status: `{payload['status']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Finite spectra exported: `{payload['finite_spectra_exported']}`",
        f"Safe for official gate: `{payload['safe_for_official_gate']}`",
        "",
        "## Deltas vs integrated negative-imprint branch",
    ]
    for key, value in payload["deltas_vs_integrated_negative_imprint_branch"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
