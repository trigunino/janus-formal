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
    lensing_weyl_source,
    primordial_power,
    solve_photon_baryon_sources,
    transfer_for_ell,
)
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import _metrics, _spectra_from_sources, _tight_quadrupole_sources
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_geometric_cmb_idea_screen.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_geometric_cmb_idea_screen.json")


def _reflect_time(arr: np.ndarray) -> np.ndarray:
    return arr[:, ::-1]


def _source_with_weyl_mirror(k_grid: np.ndarray, eta: np.ndarray) -> tuple:
    theta0, vb, psi, psi_dot, pol_quad, _weyl = solve_photon_baryon_sources(k_grid, eta)
    weyl = lensing_weyl_source(k_grid, eta)
    even = 0.5 * (weyl + _reflect_time(weyl))
    odd = 0.5 * (weyl - _reflect_time(weyl))
    weyl_obs = even + math.cos(math.pi / 2.0) * odd
    return theta0, vb, psi, psi_dot, pol_quad, weyl_obs


def _source_with_swisw_memory(k_grid: np.ndarray, eta: np.ndarray) -> tuple:
    theta0, vb, psi, psi_dot, pol_quad, weyl = solve_photon_baryon_sources(k_grid, eta)
    even_dot = 0.5 * (psi_dot + _reflect_time(psi_dot))
    odd_dot = 0.5 * (psi_dot - _reflect_time(psi_dot))
    psi_dot_obs = even_dot + math.cos(math.pi / 2.0) * odd_dot
    return theta0, vb, psi, psi_dot_obs, pol_quad, weyl


def _transport_cls(k_grid: np.ndarray, eta: np.ndarray, ell_grid: list[int]) -> tuple[dict, dict]:
    pk = primordial_power(k_grid)
    shear = solve_photon_baryon_sources(k_grid, eta)
    tight = _tight_quadrupole_sources(k_grid, eta)
    rows = []
    hidden_rows = []
    for ell in ell_grid:
        tt_s, ee_s, pp_s = transfer_for_ell(ell, k_grid, eta, shear)
        _tt_t, ee_t, _pp_t = transfer_for_ell(ell, k_grid, eta, tight)
        e_even = 0.5 * (ee_s + ee_t)
        e_odd = 0.5 * (ee_t - ee_s)
        e_obs = e_even
        rows.append(
            {
                "ell": float(ell),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * tt_s * tt_s, np.log(k_grid))),
                "te": float(4.0 * math.pi * np.trapezoid(pk * tt_s * e_obs, np.log(k_grid))),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * e_obs * e_obs, np.log(k_grid))),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * pp_s * pp_s, np.log(k_grid))),
            }
        )
        hidden_rows.append(
            {
                "ell": float(ell),
                "bb_hidden": float(4.0 * math.pi * np.trapezoid(pk * e_odd * e_odd, np.log(k_grid))),
                "ee_plus_bb": float(4.0 * math.pi * np.trapezoid(pk * (e_even * e_even + e_odd * e_odd), np.log(k_grid))),
            }
        )
    cls = {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}
    hidden = {key: np.array([row[key] for row in hidden_rows], dtype=float) for key in ["ell", "bb_hidden", "ee_plus_bb"]}
    return cls, hidden


def _lowtt_score(cls: dict) -> dict:
    return band_score(cls["ell"], cls["tt"], "tt", 2, 29)


def _lensing_score(cls: dict) -> dict:
    return band_score(cls["ell"], cls["pp"], "pp", 8, 400)


def _delta(new: float, old: float) -> float:
    return float(new - old)


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    baseline_sources = solve_photon_baryon_sources(k_grid, eta)
    baseline_cls = _spectra_from_sources(baseline_sources, k_grid, eta, ell_grid)
    baseline_metrics = _metrics(baseline_cls)
    baseline_lowtt = _lowtt_score(baseline_cls)
    baseline_lensing = _lensing_score(baseline_cls)

    transport_cls, hidden = _transport_cls(k_grid, eta, ell_grid)
    transport_metrics = _metrics(transport_cls)
    hidden_fraction = float(
        np.trapezoid(hidden["bb_hidden"], hidden["ell"]) /
        max(np.trapezoid(hidden["ee_plus_bb"], hidden["ell"]), 1.0e-30)
    )

    weyl_cls = _spectra_from_sources(_source_with_weyl_mirror(k_grid, eta), k_grid, eta, ell_grid)
    swisw_cls = _spectra_from_sources(_source_with_swisw_memory(k_grid, eta), k_grid, eta, ell_grid)
    weyl_lensing = _lensing_score(weyl_cls)
    swisw_lowtt = _lowtt_score(swisw_cls)

    eb_hidden = {
        "te_delta": _delta(transport_metrics["highl_te_shape"]["chi2_per_dof"], baseline_metrics["highl_te_shape"]["chi2_per_dof"]),
        "ee_delta": _delta(transport_metrics["highl_ee_shape"]["chi2_per_dof"], baseline_metrics["highl_ee_shape"]["chi2_per_dof"]),
        "te_zero_delta": len(transport_metrics["te_zero_crossings"]) - len(baseline_metrics["te_zero_crossings"]),
        "hidden_bb_fraction": hidden_fraction,
        "passes": bool(
            transport_metrics["highl_te_shape"]["chi2_per_dof"] < baseline_metrics["highl_te_shape"]["chi2_per_dof"]
            and transport_metrics["highl_ee_shape"]["chi2_per_dof"] <= baseline_metrics["highl_ee_shape"]["chi2_per_dof"]
            and hidden_fraction > 0.0
        ),
    }
    weyl_projection = {
        "lensing_chi2_per_dof_delta": _delta(weyl_lensing["chi2_per_dof"], baseline_lensing["chi2_per_dof"]),
        "passes": bool(weyl_lensing["chi2_per_dof"] < baseline_lensing["chi2_per_dof"]),
    }
    swisw_memory = {
        "lowtt_chi2_per_dof_delta": _delta(swisw_lowtt["chi2_per_dof"], baseline_lowtt["chi2_per_dof"]),
        "passes": bool(swisw_lowtt["chi2_per_dof"] < baseline_lowtt["chi2_per_dof"]),
    }

    return {
        "status": "janus-z4-geometric-cmb-idea-screen",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "fixed_geometric_choices": {
            "membrane_a_sigma": "2/3",
            "z4_quarter_turn": "pi/2",
            "no_continuous_fit_factor": True,
        },
        "eb_hidden_conservation": eb_hidden,
        "weyl_lensing_mirror_projection": weyl_projection,
        "swisw_membrane_memory": swisw_memory,
        "recommended_next_branches": [
            name for name, row in [
                ("eb_hidden_conservation", eb_hidden),
                ("weyl_lensing_mirror_projection", weyl_projection),
                ("swisw_membrane_memory", swisw_memory),
            ]
            if row["passes"]
        ],
        "observational_planck_gate_passed": False,
        "verdict": (
            "This screen evaluates fixed Z4/orbifold mechanisms only. Passing here means a branch "
            "is worth controlled solver integration; it is not a Planck validation."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Geometric CMB Idea Screen",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Recommended branches: `{payload['recommended_next_branches']}`",
        "",
    ]
    for name in ["eb_hidden_conservation", "weyl_lensing_mirror_projection", "swisw_membrane_memory"]:
        lines.append(f"## {name}")
        for key, value in payload[name].items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.append(payload["verdict"])
    lines.append("")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
