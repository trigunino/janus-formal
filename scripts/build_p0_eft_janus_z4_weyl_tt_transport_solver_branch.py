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
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import optical_window, primordial_power, visibility


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_solver_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_solver_branch.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_solver_branch_spectra.csv")
FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]


def _reflect_time(arr: np.ndarray) -> np.ndarray:
    return arr[:, ::-1]


def _transfer_for_ell(
    ell: int,
    k_grid: np.ndarray,
    eta: np.ndarray,
    sources: tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray],
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    eta0 = 14000.0
    theta0, vb, psi, psi_dot, pol_quad, weyl = sources
    psi_dot_mirror = _reflect_time(psi_dot)
    weyl_mirror = _reflect_time(weyl)
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
    clock_regularizer = -low_l_window * 2.0 * psi_dot_mirror
    tt_source = (
        g[None, :] * (theta0 + psi) * j
        + g[None, :] * vb * jp
        + e_tau[None, :] * (2.0 * psi_dot + clock_regularizer) * j
    )
    e_source = g[None, :] * pol_quad * e_kernel
    weyl_even = 0.5 * (weyl + weyl_mirror)
    lens_source = lens_kernel[None, :] * weyl_even * j
    return (
        np.trapezoid(tt_source, eta, axis=1),
        np.trapezoid(e_source, eta, axis=1),
        np.trapezoid(lens_source, eta, axis=1),
    )


def _assemble_branch(ell_grid: list[int], k_grid: np.ndarray, eta: np.ndarray) -> dict[str, np.ndarray]:
    sources = _geometric_sources(k_grid, eta)
    pk = primordial_power(k_grid) * _imprint_weight(k_grid, "jeans_blue")
    log_k = np.log(k_grid)
    rows = []
    for ell in ell_grid:
        tt_t, ee_t, pp_t = _transfer_for_ell(ell, k_grid, eta, sources)
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
    safe = bool(
        finite and
        deltas["lowTT"] <= 0.0 and
        deltas["lensing"] <= 0.0 and
        deltas["highl_TT_peak1"] <= 0.5 and
        deltas["highl_TE"] <= 1.0 and
        deltas["highl_EE"] <= 1.0
    )
    return {
        "status": "janus-z4-weyl-tt-transport-solver-branch",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "mechanisms": [
            "mirror-even Weyl lensing source",
            "low-l TT Ward clock regularizer",
            "controlled geometric branch",
            "fixed jeans_blue negative-sector primordial imprint",
        ],
        "spectra_path": str(SPECTRA_PATH),
        "finite_spectra_exported": bool(finite),
        "integrated_shape": integrated_shape,
        "branch_shape": branch_shape,
        "deltas_vs_integrated_negative_imprint_branch": deltas,
        "safe_for_official_gate": safe,
        "observational_planck_gate_passed": False,
        "next": "Run dedicated Planck gate if safe_for_official_gate is true.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl / TT Transport Solver Branch",
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
