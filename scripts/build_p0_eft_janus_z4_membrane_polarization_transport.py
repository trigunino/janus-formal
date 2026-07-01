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
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import (
    _metrics,
    _tight_quadrupole_sources,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_membrane_polarization_transport.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_membrane_polarization_transport.json")


def _transport_spectra(
    k_grid: np.ndarray,
    eta: np.ndarray,
    ell_grid: list[int],
    alpha_h: float,
    odd_sign: float,
) -> dict[str, np.ndarray]:
    pk = primordial_power(k_grid)
    shear_sources = solve_photon_baryon_sources(k_grid, eta)
    tight_sources = _tight_quadrupole_sources(k_grid, eta)
    rows = []
    for ell in ell_grid:
        tt_s, ee_s, pp_s = transfer_for_ell(ell, k_grid, eta, shear_sources)
        _tt_t, ee_t, _pp_t = transfer_for_ell(ell, k_grid, eta, tight_sources)
        ee_even = 0.5 * (ee_s + ee_t)
        ee_odd = 0.5 * (ee_t - ee_s)
        ee_obs = ee_even + odd_sign * math.cos(alpha_h) * ee_odd
        rows.append(
            {
                "ell": float(ell),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * tt_s * tt_s, np.log(k_grid))),
                "te": float(4.0 * math.pi * np.trapezoid(pk * tt_s * ee_obs, np.log(k_grid))),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * ee_obs * ee_obs, np.log(k_grid))),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * pp_s * pp_s, np.log(k_grid))),
            }
        )
    return {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}


def _score(metrics: dict, baseline: dict) -> dict:
    te_delta = metrics["highl_te_shape"]["chi2_per_dof"] - baseline["highl_te_shape"]["chi2_per_dof"]
    ee_delta = metrics["highl_ee_shape"]["chi2_per_dof"] - baseline["highl_ee_shape"]["chi2_per_dof"]
    tt_delta = abs(metrics["highl_tt_peak"]["ell_shift"]) - abs(baseline["highl_tt_peak"]["ell_shift"])
    te_zero_delta = len(metrics["te_zero_crossings"]) - len(baseline["te_zero_crossings"])
    return {
        "highl_te_chi2_per_dof_delta": float(te_delta),
        "highl_ee_chi2_per_dof_delta": float(ee_delta),
        "tt_peak_abs_shift_delta": int(tt_delta),
        "te_zero_crossing_count_delta": int(te_zero_delta),
        "te_restored": bool(te_delta < 0.0 and te_zero_delta > 0),
        "ee_preserved_or_improved": bool(ee_delta <= 0.0),
        "tt_unchanged": bool(tt_delta == 0),
    }


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    baseline = _metrics(_transport_spectra(k_grid, eta, ell_grid, 0.0, -1.0))

    branches = [
        ("identity_tight", 0.0, 1.0),
        ("orbifold_reflection", 0.0, -1.0),
        ("z4_quarter_turn", math.pi / 2.0, 1.0),
    ]
    rows = []
    for name, alpha_h, odd_sign in branches:
        metrics = _metrics(_transport_spectra(k_grid, eta, ell_grid, alpha_h, odd_sign))
        rows.append(
            {
                "name": name,
                "alpha_H": "pi/2" if math.isclose(alpha_h, math.pi / 2.0) else "0",
                "odd_sign": int(odd_sign),
                "metrics": metrics,
                "score": _score(metrics, baseline),
            }
        )

    z4_branch = next(row for row in rows if row["name"] == "z4_quarter_turn")
    z4_score = z4_branch["score"]
    safe = bool(z4_score["te_restored"] and z4_score["ee_preserved_or_improved"] and z4_score["tt_unchanged"])

    return {
        "status": "janus-z4-membrane-polarization-transport",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "membrane": {"a_sigma": "2/3", "z_sigma": "1/2"},
        "transport_model": "post-source tetrad memory: E_obs=E_even+sign*cos(alpha_H)*E_odd",
        "z4_generator_angle": "pi/2",
        "baseline": baseline,
        "branches": rows,
        "z4_quarter_turn": z4_branch,
        "safe_solver_integration_recommended": safe,
        "observational_planck_gate_passed": False,
        "verdict": (
            "The Z4 membrane transport branch is accepted only if the quarter-turn "
            "restores TE, preserves or improves EE, and leaves TT peak phase unchanged."
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
    z4 = payload["z4_quarter_turn"]
    lines = [
        "# Janus Z4 Membrane Polarization Transport",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Membrane: `a_sigma={payload['membrane']['a_sigma']}`, `z_sigma={payload['membrane']['z_sigma']}`",
        f"Z4 generator angle: `{payload['z4_generator_angle']}`",
        f"Safe solver integration recommended: `{payload['safe_solver_integration_recommended']}`",
        "",
        "## Z4 Quarter-Turn Score",
    ]
    for key, value in z4["score"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
