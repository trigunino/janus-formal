from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_negative_sector_cmb_imprint import _controlled_transfers, _imprint_weight
from scripts.build_p0_eft_janus_z4_controlled_geometric_solver_branch import _assemble_branch, _shape_summary
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import primordial_power, solve_photon_baryon_sources
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import _spectra_from_sources


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_branch.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_branch_spectra.csv")
MODE = "jeans_blue"
FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]


def _assemble_integrated(ell_grid: list[int], k_grid: np.ndarray, eta: np.ndarray) -> dict[str, np.ndarray]:
    transfers, _hidden = _controlled_transfers(ell_grid, k_grid, eta)
    pk = primordial_power(k_grid) * _imprint_weight(k_grid, MODE)
    log_k = np.log(k_grid)
    rows = []
    for row in transfers["transfers"]:
        rows.append(
            {
                "ell": float(row["ell"]),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * row["tt_t"] * row["tt_t"], log_k)),
                "te": float(4.0 * math.pi * np.trapezoid(pk * row["tt_t"] * row["ee_t"], log_k)),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * row["ee_t"] * row["ee_t"], log_k)),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * row["pp_t"] * row["pp_t"], log_k)),
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
    baseline_cls = _spectra_from_sources(solve_photon_baryon_sources(k_grid, eta), k_grid, eta, ell_grid)
    controlled_cls, _hidden = _assemble_branch(ell_grid, k_grid, eta)
    integrated_cls = _assemble_integrated(ell_grid, k_grid, eta)

    baseline_shape = _shape_summary(baseline_cls)
    controlled_shape = _shape_summary(controlled_cls)
    integrated_shape = _shape_summary(integrated_cls)
    deltas_vs_controlled = _delta_summary(integrated_shape, controlled_shape)
    deltas_vs_baseline = _delta_summary(integrated_shape, baseline_shape)

    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        for idx, ell in enumerate(integrated_cls["ell"]):
            writer.writerow(
                {
                    "ell": int(ell),
                    "cl_tt": integrated_cls["tt"][idx],
                    "cl_te": integrated_cls["te"][idx],
                    "cl_ee": integrated_cls["ee"][idx],
                    "cl_pp": integrated_cls["pp"][idx],
                }
            )

    finite = all(np.isfinite(integrated_cls[key]).all() for key in ["tt", "te", "ee", "pp"])
    return {
        "status": "janus-z4-integrated-negative-imprint-branch",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "integrated_mechanisms": [
            "E/B hidden membrane transport",
            "Weyl mirror projection",
            "negative-sector primordial jeans_blue imprint",
        ],
        "fixed_choices": {
            "negative_imprint_mode": MODE,
            "scale_ratio": 100.0,
            "c_ratio": 10.0,
            "no_continuous_fit_factor": True,
        },
        "spectra_path": str(SPECTRA_PATH),
        "finite_spectra_exported": bool(finite),
        "ell_min": int(integrated_cls["ell"][0]),
        "ell_max": int(integrated_cls["ell"][-1]),
        "baseline_shape": baseline_shape,
        "controlled_shape": controlled_shape,
        "integrated_shape": integrated_shape,
        "deltas_vs_controlled_branch": deltas_vs_controlled,
        "deltas_vs_baseline": deltas_vs_baseline,
        "safe_for_official_gate": bool(
            finite and
            deltas_vs_controlled["highl_TT_peak1"] < 0.0 and
            deltas_vs_controlled["highl_TE"] <= 1.0 and
            deltas_vs_controlled["highl_EE"] <= 1.0
        ),
        "observational_planck_gate_passed": False,
        "next": "Run official Planck gates with this CSV as JanusZ4NativeBoltzmann.spectra_path.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Integrated Negative Imprint Branch",
        "",
        f"Status: `{payload['status']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Finite spectra exported: `{payload['finite_spectra_exported']}`",
        f"Safe for official gate: `{payload['safe_for_official_gate']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        "",
        "## Deltas vs controlled branch",
    ]
    for key, value in payload["deltas_vs_controlled_branch"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
