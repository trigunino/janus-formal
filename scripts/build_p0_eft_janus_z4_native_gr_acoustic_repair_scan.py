from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_native_gr_decomposition_gate import _load_rows, _zero_crossings
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _camb_reference, _fit_shape, _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_acoustic_repair_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_acoustic_repair_scan.json")


def _best_projection_warp(ell: np.ndarray, native: np.ndarray, reference: np.ndarray) -> dict:
    best: dict | None = None
    for scale in np.linspace(0.70, 1.35, 66):
        warped = np.interp(ell * scale, ell, native, left=np.nan, right=np.nan)
        mask = (ell >= 30.0) & (ell <= 1200.0) & np.isfinite(warped)
        row = _fit_shape(warped[mask], reference[mask])
        score = float(row.get("chi2_per_dof", 1.0e99))
        candidate = {
            "projection_scale": float(scale),
            "chi2_per_dof": score,
            "best_shape_amplitude": row.get("best_shape_amplitude"),
            "max_abs_fractional_residual": row.get("max_abs_fractional_residual"),
        }
        if best is None or score < best["chi2_per_dof"]:
            best = candidate
    assert best is not None
    best["ok"] = bool(best["chi2_per_dof"] < 5.0)
    return best


def build_payload() -> dict:
    rows = _load_rows()
    ell = np.array([row["ell"] for row in rows], dtype=float)
    camb = _camb_reference(ell)
    native = {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
    }
    tt_projection = _best_projection_warp(ell, native["tt"], camb["tt"])
    ee_projection = _best_projection_warp(ell, native["ee"], camb["ee"])
    te_projection = _best_projection_warp(ell, native["te"], camb["te"])
    native_te_zeros = _zero_crossings(ell, native["te"])
    camb_te_zeros = _zero_crossings(ell, camb["te"])
    projection_only_sufficient = bool(
        tt_projection["ok"]
        and ee_projection["ok"]
        and te_projection["ok"]
        and len(native_te_zeros) >= max(1, len(camb_te_zeros) // 2)
    )
    return {
        "status": "janus-z4-native-gr-acoustic-repair-scan",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "projection_only_hypothesis_tested": True,
        "tt_projection_scan": tt_projection,
        "te_projection_scan": te_projection,
        "ee_projection_scan": ee_projection,
        "native_te_zero_crossings": native_te_zeros,
        "camb_te_zero_crossings": camb_te_zeros,
        "projection_only_sufficient": projection_only_sufficient,
        "native_source_repair_required": not projection_only_sufficient,
        "next_required_action": (
            "derive or replace the native GR LOS source engine; ell/projection warping alone cannot repair the baseline"
            if not projection_only_sufficient
            else "apply the projection repair and rerun the native GR reference gate"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Native GR Acoustic Repair Scan",
        "",
        f"Projection-only sufficient: `{payload['projection_only_sufficient']}`",
        f"Native source repair required: `{payload['native_source_repair_required']}`",
        "",
        "## Best Projection Warps",
        f"- TT: scale `{payload['tt_projection_scan']['projection_scale']}`, chi2/dof `{payload['tt_projection_scan']['chi2_per_dof']}`",
        f"- TE: scale `{payload['te_projection_scan']['projection_scale']}`, chi2/dof `{payload['te_projection_scan']['chi2_per_dof']}`",
        f"- EE: scale `{payload['ee_projection_scan']['projection_scale']}`, chi2/dof `{payload['ee_projection_scan']['chi2_per_dof']}`",
        "",
        "## TE Zero Crossings",
        f"- native: `{payload['native_te_zero_crossings']}`",
        f"- CAMB: `{payload['camb_te_zero_crossings']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
