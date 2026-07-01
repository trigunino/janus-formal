from __future__ import annotations

from pathlib import Path
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import assemble_spectra
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_source_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_source_scan.json")


def _dense_from_rows(rows: list[dict[str, float]]) -> dict[str, np.ndarray]:
    sparse_ell = np.array([row["ell"] for row in rows], dtype=float)
    ell = np.arange(int(sparse_ell[-1]) + 1, dtype=float)

    def dense(column: str) -> np.ndarray:
        sparse = np.array([row[column] for row in rows], dtype=float)
        values = np.interp(ell, sparse_ell, sparse, left=0.0, right=sparse[-1])
        values[:2] = 0.0
        return values

    cls = {"ell": ell, "tt": dense("cl_tt"), "te": dense("cl_te"), "ee": dense("cl_ee")}
    factor = ell * (ell + 1.0) / (2.0 * np.pi)
    t_cmb = 2.7255e6
    peak_mask = (ell >= 150.0) & (ell <= 320.0)
    peak = float(np.nanmax(cls["tt"][peak_mask] * factor[peak_mask] * t_cmb * t_cmb))
    scalar_scale = 5600.0 / peak if peak > 0.0 else 1.0
    for key in ("tt", "te", "ee"):
        cls[key] = cls[key] * scalar_scale * factor * t_cmb * t_cmb
    return cls


def _zero_crossings(ell: np.ndarray, values: np.ndarray, ell_min: int, ell_max: int) -> int:
    mask = (ell >= ell_min) & (ell <= ell_max)
    v = values[mask]
    return int(sum(1 for idx in range(len(v) - 1) if v[idx] * v[idx + 1] < 0.0))


def score_model(model: str, hybrid_weight: float = 0.0) -> dict:
    rows = assemble_spectra(polarization_model=model, polarization_hybrid_weight=hybrid_weight)
    cls = _dense_from_rows(rows)
    ell = cls["ell"]
    te = band_score(ell, cls["te"], "te", 30, 1200)
    ee = band_score(ell, cls["ee"], "ee", 30, 1200)
    lowe = band_score(ell, cls["ee"], "ee", 2, 29)
    return {
        "model": model,
        "hybrid_weight": hybrid_weight,
        "te_chi2_per_dof": te["chi2_per_dof"],
        "ee_chi2_per_dof": ee["chi2_per_dof"],
        "lowe_chi2_per_dof": lowe["chi2_per_dof"],
        "te_zero_crossings": _zero_crossings(ell, cls["te"], 30, 1200),
        "finite": all(math.isfinite(float(row[field])) for row in rows for field in ("cl_tt", "cl_te", "cl_ee", "cl_pp")),
    }


def build_payload() -> dict:
    rows = [score_model("shear"), score_model("quadrupole")]
    rows.extend(score_model("hybrid", weight) for weight in (0.15, 0.30, 0.50, 0.70))
    best_te_phase = max(rows, key=lambda row: row["te_zero_crossings"])
    best_shape = min(rows, key=lambda row: row["te_chi2_per_dof"] + row["ee_chi2_per_dof"] + row["lowe_chi2_per_dof"])
    best_nontrivial_phase = min(
        (row for row in rows if row["te_zero_crossings"] > 0),
        key=lambda row: row["te_chi2_per_dof"] + row["ee_chi2_per_dof"] + row["lowe_chi2_per_dof"],
        default=None,
    )
    return {
        "status": "janus-z4-polarization-source-scan",
        "native_z4_solver_used": True,
        "official_planck_likelihood_executed": False,
        "compressed_lcdm_parameters_used": False,
        "rows": rows,
        "best_te_phase_model": best_te_phase["model"],
        "best_te_phase_weight": best_te_phase["hybrid_weight"],
        "best_shape_model": best_shape["model"],
        "best_shape_weight": best_shape["hybrid_weight"],
        "best_nontrivial_phase_model": None if best_nontrivial_phase is None else best_nontrivial_phase["model"],
        "best_nontrivial_phase_weight": None if best_nontrivial_phase is None else best_nontrivial_phase["hybrid_weight"],
        "active_solver_model": "shear",
        "quadrupole_kept_as_candidate": True,
        "polarization_source_scan_ready": True,
        "verdict": (
            "Hybrid scans test whether TE phase can be restored without losing shape. "
            "The active shear source remains the default until a candidate improves "
            "shape and official Planck gates simultaneously."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Polarization Source Scan",
        "",
        f"Status: `{payload['status']}`",
        f"Active solver model: `{payload['active_solver_model']}`",
        f"Best TE phase model: `{payload['best_te_phase_model']}` weight `{payload['best_te_phase_weight']}`",
        f"Best shape model: `{payload['best_shape_model']}` weight `{payload['best_shape_weight']}`",
        f"Best nontrivial-phase model: `{payload['best_nontrivial_phase_model']}` "
        f"weight `{payload['best_nontrivial_phase_weight']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        lines.append(
            f"- `{row['model']}` weight `{row['hybrid_weight']}`: TE zeros `{row['te_zero_crossings']}`, "
            f"TE chi2/dof `{row['te_chi2_per_dof']:.6g}`, "
            f"EE chi2/dof `{row['ee_chi2_per_dof']:.6g}`, "
            f"lowE chi2/dof `{row['lowe_chi2_per_dof']:.6g}`"
        )
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
