from __future__ import annotations

from pathlib import Path
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_controlled_geometric_solver_branch import _assemble_branch, _shape_summary
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import primordial_power, solve_photon_baryon_sources
from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import _spectra_from_sources


REPORT_PATH = Path("outputs/reports/p0_eft_janus_negative_sector_cmb_imprint.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_negative_sector_cmb_imprint.json")

SCALE_RATIO = 100.0
C_RATIO = 10.0


def _imprint_weight(k_grid: np.ndarray, mode: str) -> np.ndarray:
    pivot = 0.05
    x = np.log(np.maximum(k_grid / pivot, 1.0e-12))
    period = math.log(SCALE_RATIO)
    if mode == "log_harmonic":
        amp = 1.0 / math.log(SCALE_RATIO)
        return np.square(1.0 + amp * np.cos(2.0 * math.pi * x / period))
    if mode == "jeans_blue":
        k_j = pivot / math.sqrt(C_RATIO)
        return 1.0 + (1.0 / math.log(SCALE_RATIO)) * np.square(k_grid / (k_grid + k_j))
    if mode == "jeans_notch":
        k_j = pivot / math.sqrt(C_RATIO)
        width = 1.0 / math.sqrt(math.log(SCALE_RATIO))
        notch = np.exp(-0.5 * np.square(np.log(np.maximum(k_grid / k_j, 1.0e-12)) / width))
        return np.maximum(1.0 - (1.0 / C_RATIO) * notch, 1.0e-6)
    raise ValueError(mode)


def _spectra_with_imprint(cls_transfers: dict, hidden: dict, k_grid: np.ndarray, eta_log_k: np.ndarray, mode: str) -> dict:
    del hidden
    weight = _imprint_weight(k_grid, mode)
    pk = primordial_power(k_grid) * weight
    rows = []
    transfers = cls_transfers["transfers"]
    for row in transfers:
        rows.append(
            {
                "ell": float(row["ell"]),
                "tt": float(4.0 * math.pi * np.trapezoid(pk * row["tt_t"] * row["tt_t"], eta_log_k)),
                "te": float(4.0 * math.pi * np.trapezoid(pk * row["tt_t"] * row["ee_t"], eta_log_k)),
                "ee": float(4.0 * math.pi * np.trapezoid(pk * row["ee_t"] * row["ee_t"], eta_log_k)),
                "pp": float(4.0 * math.pi * np.trapezoid(pk * row["pp_t"] * row["pp_t"], eta_log_k)),
            }
        )
    return {key: np.array([row[key] for row in rows], dtype=float) for key in ["ell", "tt", "te", "ee", "pp"]}


def _controlled_transfers(ell_grid: list[int], k_grid: np.ndarray, eta: np.ndarray) -> tuple[dict, dict]:
    from scripts.build_p0_eft_janus_z4_controlled_geometric_solver_branch import _geometric_sources
    from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import transfer_for_ell

    sources = _geometric_sources(k_grid, eta)
    rows = []
    for ell in ell_grid:
        tt_t, ee_t, pp_t = transfer_for_ell(ell, k_grid, eta, sources)
        rows.append({"ell": ell, "tt_t": tt_t, "ee_t": ee_t, "pp_t": pp_t})
    return {"transfers": rows}, {}


def _peak_shift(shape: dict) -> int:
    pulls = shape["highl_TT_peak1"]["dominant_pulls"]
    return int(pulls[0]["ell"]) if pulls else -1


def build_payload() -> dict:
    ell_grid = sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200]))
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    log_k = np.log(k_grid)

    baseline_cls = _spectra_from_sources(solve_photon_baryon_sources(k_grid, eta), k_grid, eta, ell_grid)
    controlled_cls, hidden = _assemble_branch(ell_grid, k_grid, eta)
    controlled_transfers, _hidden = _controlled_transfers(ell_grid, k_grid, eta)
    baseline_shape = _shape_summary(baseline_cls)
    controlled_shape = _shape_summary(controlled_cls)

    rows = []
    for mode in ["log_harmonic", "jeans_blue", "jeans_notch"]:
        cls = _spectra_with_imprint(controlled_transfers, hidden, k_grid, log_k, mode)
        shape = _shape_summary(cls)
        deltas = {
            key: float(shape[key]["chi2_per_dof"] - controlled_shape[key]["chi2_per_dof"])
            for key in ["lowTT", "highl_TT_peak1", "highl_TE", "highl_EE", "lensing"]
        }
        rows.append(
            {
                "mode": mode,
                "shape": shape,
                "deltas_vs_controlled_branch": deltas,
                "tt_improved": bool(deltas["highl_TT_peak1"] < 0.0),
                "polarization_not_destroyed": bool(deltas["highl_TE"] <= 1.0 and deltas["highl_EE"] <= 1.0),
            }
        )

    accepted = [
        row for row in rows
        if row["tt_improved"] and row["polarization_not_destroyed"]
    ]
    best_promotable = (
        min(accepted, key=lambda row: row["deltas_vs_controlled_branch"]["highl_TT_peak1"])
        if accepted else None
    )
    best_tt_only = min(rows, key=lambda row: (not row["tt_improved"], row["deltas_vs_controlled_branch"]["highl_TT_peak1"]))
    return {
        "status": "janus-negative-sector-cmb-imprint",
        "source_reference": {
            "local_pdf": r"C:\Users\alzie\Downloads\The Janus Cosmological Model and the Fluctuations  of the CMB.pdf",
            "hypothesis": "negative-sector Jeans/imprint can seed positive-sector CMB fluctuations",
            "fixed_scale_ratio": SCALE_RATIO,
            "fixed_c_ratio": C_RATIO,
        },
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "branch_only_diagnostic": True,
        "continuous_fit_factor_used": False,
        "baseline_shape": baseline_shape,
        "controlled_branch_shape": controlled_shape,
        "candidates": rows,
        "accepted_candidate_count": len(accepted),
        "best_promotable_candidate": best_promotable,
        "best_tt_only_candidate": best_tt_only,
        "safe_to_promote": bool(len(accepted) > 0),
        "observational_planck_gate_passed": False,
        "verdict": (
            "Fixed negative-sector imprint candidates are tested as primordial-shape hypotheses. "
            "A candidate is promotable only if it improves TT peak shape without destroying TE/EE."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    best = payload["best_promotable_candidate"] or payload["best_tt_only_candidate"]
    lines = [
        "# Janus Negative-Sector CMB Imprint",
        "",
        f"Status: `{payload['status']}`",
        f"Scale ratio: `{payload['source_reference']['fixed_scale_ratio']}`",
        f"c ratio: `{payload['source_reference']['fixed_c_ratio']}`",
        f"Continuous fit factor used: `{payload['continuous_fit_factor_used']}`",
        f"Accepted candidates: `{payload['accepted_candidate_count']}`",
        f"Safe to promote: `{payload['safe_to_promote']}`",
        "",
        "## Best Candidate",
        f"- mode: `{best['mode']}`",
    ]
    for key, value in best["deltas_vs_controlled_branch"].items():
        lines.append(f"- `{key}` delta: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
