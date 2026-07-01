from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    lensing_weyl_source,
    primordial_power,
    solve_photon_baryon_sources,
    transfer_for_ell,
)
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import (
    _metrics,
    _spectra_from_sources,
    _tight_quadrupole_sources,
)
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_controlled_geometric_solver_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_controlled_geometric_solver_branch.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_controlled_geometric_solver_branch_spectra.csv")


def _reflect_time(arr: np.ndarray) -> np.ndarray:
    return arr[:, ::-1]


def _geometric_sources(k_grid: np.ndarray, eta: np.ndarray) -> tuple:
    theta0, vb, psi, psi_dot, shear_pol, _weyl = solve_photon_baryon_sources(k_grid, eta)
    _t0, _v, _p, _pd, tight_pol, _w = _tight_quadrupole_sources(k_grid, eta)
    e_even = 0.5 * (shear_pol + tight_pol)
    weyl = lensing_weyl_source(k_grid, eta)
    weyl_even = 0.5 * (weyl + _reflect_time(weyl))
    return theta0, vb, psi, psi_dot, e_even, weyl_even


def _assemble_branch(ell_grid: list[int], k_grid: np.ndarray, eta: np.ndarray) -> tuple[dict[str, np.ndarray], dict[str, np.ndarray]]:
    pk = primordial_power(k_grid)
    shear = solve_photon_baryon_sources(k_grid, eta)
    tight = _tight_quadrupole_sources(k_grid, eta)
    geom = _geometric_sources(k_grid, eta)
    rows = []
    hidden_rows = []
    for ell in ell_grid:
        tt_t, ee_t, pp_t = transfer_for_ell(ell, k_grid, eta, geom)
        _tt_s, ee_s, _pp_s = transfer_for_ell(ell, k_grid, eta, shear)
        _tt_q, ee_q, _pp_q = transfer_for_ell(ell, k_grid, eta, tight)
        e_odd = 0.5 * (ee_q - ee_s)
        rows.append(
            {
                "ell": float(ell),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * tt_t * tt_t, np.log(k_grid))),
                "te": float(4.0 * math.pi * np.trapezoid(pk * tt_t * ee_t, np.log(k_grid))),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * ee_t * ee_t, np.log(k_grid))),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * pp_t * pp_t, np.log(k_grid))),
            }
        )
        hidden_rows.append(
            {
                "ell": float(ell),
                "bb_hidden": float(4.0 * math.pi * np.trapezoid(pk * e_odd * e_odd, np.log(k_grid))),
            }
        )
    cls = {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}
    hidden = {key: np.array([row[key] for row in hidden_rows], dtype=float) for key in ["ell", "bb_hidden"]}
    return cls, hidden


def _shape_summary(cls: dict[str, np.ndarray]) -> dict:
    ell = cls["ell"]
    return {
        "lowTT": band_score(ell, cls["tt"], "tt", 2, 29),
        "highl_TT_peak1": band_score(ell, cls["tt"], "tt", 30, 450),
        "highl_TE": band_score(ell, cls["te"], "te", 30, 1200),
        "highl_EE": band_score(ell, cls["ee"], "ee", 30, 1200),
        "lensing": band_score(ell, cls["pp"], "pp", 8, 400),
    }


def _delta_summary(branch: dict, baseline: dict) -> dict:
    return {
        key: float(branch[key]["chi2_per_dof"] - baseline[key]["chi2_per_dof"])
        for key in ["lowTT", "highl_TT_peak1", "highl_TE", "highl_EE", "lensing"]
    }


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    baseline_cls = _spectra_from_sources(solve_photon_baryon_sources(k_grid, eta), k_grid, eta, ell_grid)
    branch_cls, hidden = _assemble_branch(ell_grid, k_grid, eta)

    baseline_shape = _shape_summary(baseline_cls)
    branch_shape = _shape_summary(branch_cls)
    deltas = _delta_summary(branch_shape, baseline_shape)
    branch_metrics = _metrics(branch_cls)
    hidden_bb_fraction = float(
        np.trapezoid(hidden["bb_hidden"], hidden["ell"]) /
        max(np.trapezoid(branch_cls["ee"], branch_cls["ell"]) + np.trapezoid(hidden["bb_hidden"], hidden["ell"]), 1.0e-30)
    )

    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp", "cl_bb_hidden"])
        writer.writeheader()
        for idx, ell in enumerate(branch_cls["ell"]):
            writer.writerow(
                {
                    "ell": int(ell),
                    "cl_tt": branch_cls["tt"][idx],
                    "cl_te": branch_cls["te"][idx],
                    "cl_ee": branch_cls["ee"][idx],
                    "cl_pp": branch_cls["pp"][idx],
                    "cl_bb_hidden": hidden["bb_hidden"][idx],
                }
            )

    safe_shape_improved = bool(
        deltas["highl_TE"] < 0.0 and
        deltas["highl_EE"] < 0.0 and
        deltas["lensing"] < 0.0 and
        deltas["highl_TT_peak1"] <= 0.0
    )

    return {
        "status": "janus-z4-controlled-geometric-solver-branch",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "mechanisms": [
            "E/B hidden conservation from membrane Z4 quarter-turn",
            "Weyl/lensing mirror even projection",
        ],
        "fixed_geometric_choices": {
            "membrane_a_sigma": "2/3",
            "z4_quarter_turn": "pi/2",
            "no_continuous_fit_factor": True,
        },
        "spectra_path": str(SPECTRA_PATH),
        "baseline_shape": baseline_shape,
        "branch_shape": branch_shape,
        "shape_chi2_per_dof_deltas": deltas,
        "te_zero_crossings": branch_metrics["te_zero_crossings"],
        "hidden_bb_fraction": hidden_bb_fraction,
        "safe_shape_improved": safe_shape_improved,
        "observational_planck_gate_passed": False,
        "verdict": (
            "The fixed Z4 geometric branch is worth official-gate execution only if it improves "
            "TE, EE, lensing and does not worsen TT peak shape. This report is branch-only."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Controlled Geometric Solver Branch",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Safe shape improved: `{payload['safe_shape_improved']}`",
        f"Hidden BB fraction: `{payload['hidden_bb_fraction']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        "",
        "## Shape chi2/dof deltas",
    ]
    for key, value in payload["shape_chi2_per_dof_deltas"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
