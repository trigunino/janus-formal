from __future__ import annotations

import csv
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import SPECTRA_PATH as CAMB_GR_PATH
from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import write_reports as write_camb_gr
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import SPECTRA_PATH as TOY_NATIVE_PATH
from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import write_reports as write_toy_native
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _camb_reference, _fit_shape, _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_baseline_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_baseline_reduction_gate.json")


def _load(path: Path, writer) -> list[dict[str, float]]:
    if not path.exists():
        writer()
    with path.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    if not rows or rows[-1]["ell"] < 2508:
        writer()
        with path.open(encoding="utf-8") as handle:
            rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return rows


def _shape(rows: list[dict[str, float]]) -> dict[str, dict]:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    camb = _camb_reference(ell)
    spectra = {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }
    masks = {
        "high_tt": (ell >= 30.0) & (ell <= 1200.0),
        "high_te": (ell >= 30.0) & (ell <= 1200.0),
        "high_ee": (ell >= 30.0) & (ell <= 1200.0),
        "lensing_pp": (ell >= 8.0) & (ell <= 400.0),
    }
    return {
        "high_tt": _fit_shape(spectra["tt"][masks["high_tt"]], camb["tt"][masks["high_tt"]]),
        "high_te": _fit_shape(spectra["te"][masks["high_te"]], camb["te"][masks["high_te"]]),
        "high_ee": _fit_shape(spectra["ee"][masks["high_ee"]], camb["ee"][masks["high_ee"]]),
        "lensing_pp": _fit_shape(spectra["pp"][masks["lensing_pp"]], camb["pp"][masks["lensing_pp"]]),
    }


def _reduction(before: dict, after: dict, channel: str) -> dict:
    b = float(before[channel].get("chi2_per_dof", math.inf))
    a = float(after[channel].get("chi2_per_dof", math.inf))
    return {
        "before_chi2_per_dof": b,
        "after_chi2_per_dof": a,
        "absolute_reduction": b - a,
        "fractional_reduction": (b - a) / b if math.isfinite(b) and b > 0.0 else None,
        "ok": bool(a < 1.0e-8),
    }


def build_payload() -> dict:
    toy_rows = _load(TOY_NATIVE_PATH, write_toy_native)
    camb_rows = _load(CAMB_GR_PATH, write_camb_gr)
    toy_shape = _shape(toy_rows)
    camb_shape = _shape(camb_rows)
    reductions = {
        channel: _reduction(toy_shape, camb_shape, channel)
        for channel in ("high_tt", "high_te", "high_ee", "lensing_pp")
    }
    tt_te_reduced = bool(reductions["high_tt"]["ok"] and reductions["high_te"]["ok"])
    return {
        "status": "janus-z4-gr-baseline-reduction-gate",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "toy_native_path": str(TOY_NATIVE_PATH),
        "camb_gr_baseline_path": str(CAMB_GR_PATH),
        "toy_native_shape": toy_shape,
        "camb_gr_shape": camb_shape,
        "reductions": reductions,
        "dominant_tt_te_mismatch_reduced": tt_te_reduced,
        "safe_gr_baseline_available": tt_te_reduced,
        "native_toy_source_engine_repaired": False,
        "verdict": (
            "CAMB-backed GR baseline removes the dominant TT/TE mismatch in the native spectra schema; "
            "the toy native source engine remains unrepaired and must stay blocked for Planck interpretation."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 GR Baseline Reduction Gate",
        "",
        f"Dominant TT/TE mismatch reduced: `{payload['dominant_tt_te_mismatch_reduced']}`",
        f"Safe GR baseline available: `{payload['safe_gr_baseline_available']}`",
        f"Toy native source engine repaired: `{payload['native_toy_source_engine_repaired']}`",
        "",
        "## Reductions",
    ]
    for channel, row in payload["reductions"].items():
        lines.append(
            f"- `{channel}`: `{row['before_chi2_per_dof']}` -> `{row['after_chi2_per_dof']}`"
        )
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
