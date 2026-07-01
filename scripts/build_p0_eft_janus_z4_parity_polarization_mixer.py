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
    solve_photon_baryon_sources,
)
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import (
    _metrics,
    _spectra_from_sources,
    _tight_quadrupole_sources,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_parity_polarization_mixer.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_parity_polarization_mixer.json")


def _mixed_sources(k_grid: np.ndarray, eta: np.ndarray, alpha: float, odd_sign: float) -> tuple:
    theta0, vb, psi, psi_dot, shear_pol, weyl = solve_photon_baryon_sources(k_grid, eta)
    _t0, _v, _p, _pd, tight_pol, _w = _tight_quadrupole_sources(k_grid, eta)
    even = 0.5 * (shear_pol + tight_pol)
    odd = 0.5 * (tight_pol - shear_pol)
    projected_odd = odd_sign * math.cos(alpha) * odd
    pol_quad = even + projected_odd
    return theta0, vb, psi, psi_dot, pol_quad, weyl


def _score(metrics: dict, baseline: dict) -> dict:
    te_delta = metrics["highl_te_shape"]["chi2_per_dof"] - baseline["highl_te_shape"]["chi2_per_dof"]
    ee_delta = metrics["highl_ee_shape"]["chi2_per_dof"] - baseline["highl_ee_shape"]["chi2_per_dof"]
    tt_shift = abs(metrics["highl_tt_peak"]["ell_shift"])
    base_tt_shift = abs(baseline["highl_tt_peak"]["ell_shift"])
    te_zero_delta = len(metrics["te_zero_crossings"]) - len(baseline["te_zero_crossings"])
    return {
        "highl_te_chi2_per_dof_delta": float(te_delta),
        "highl_ee_chi2_per_dof_delta": float(ee_delta),
        "te_zero_crossing_count_delta": int(te_zero_delta),
        "tt_peak_shift_improved": bool(tt_shift < base_tt_shift),
        "ee_norm_preserved": bool(ee_delta <= 0.0),
        "te_restored": bool(te_delta < 0.0 and te_zero_delta > 0),
    }


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)

    baseline_sources = solve_photon_baryon_sources(k_grid, eta)
    baseline = _metrics(_spectra_from_sources(baseline_sources, k_grid, eta, ell_grid))

    candidates = []
    for alpha_label, alpha in [
        ("0", 0.0),
        ("pi/6", math.pi / 6.0),
        ("pi/4", math.pi / 4.0),
        ("pi/3", math.pi / 3.0),
        ("pi/2", math.pi / 2.0),
    ]:
        for odd_sign in [-1.0, 1.0]:
            sources = _mixed_sources(k_grid, eta, alpha, odd_sign)
            metrics = _metrics(_spectra_from_sources(sources, k_grid, eta, ell_grid))
            row = {
                "alpha_H": alpha_label,
                "odd_sign": int(odd_sign),
                "metrics": metrics,
                "score": _score(metrics, baseline),
            }
            candidates.append(row)

    viable = [
        row for row in candidates
        if row["score"]["te_restored"] and row["score"]["ee_norm_preserved"]
    ]
    best = min(
        candidates,
        key=lambda row: (
            not row["score"]["te_restored"],
            not row["score"]["ee_norm_preserved"],
            row["score"]["highl_te_chi2_per_dof_delta"],
            row["score"]["highl_ee_chi2_per_dof_delta"],
        ),
    )

    return {
        "status": "janus-z4-parity-polarization-mixer",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "parity_decomposition": "E_even=(E_shear+E_tight)/2, E_odd=(E_tight-E_shear)/2",
        "holst_projection": "E_obs=E_even+sign*cos(alpha_H)*E_odd",
        "baseline": baseline,
        "candidates": candidates,
        "viable_candidate_count": len(viable),
        "best_candidate": best,
        "safe_solver_integration_recommended": bool(len(viable) > 0),
        "observational_planck_gate_passed": False,
        "verdict": (
            "The Z4 parity/Holst mixer is accepted only if TE zero crossings return, "
            "high-l TE improves and EE is not worsened. This is a branch-only diagnostic."
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
    best = payload["best_candidate"]
    lines = [
        "# Janus Z4 Parity Polarization Mixer",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Viable candidates: `{payload['viable_candidate_count']}`",
        f"Safe solver integration recommended: `{payload['safe_solver_integration_recommended']}`",
        "",
        "## Best Candidate",
        f"- alpha_H: `{best['alpha_H']}`",
        f"- odd_sign: `{best['odd_sign']}`",
    ]
    for key, value in best["score"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
