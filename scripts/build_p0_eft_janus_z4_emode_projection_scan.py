from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import FIELDS, SPECTRA_PATH, assemble_spectra
from scripts.build_p0_eft_janus_z4_official_planck_highl_gate import run_likelihood as run_highl
from scripts.build_p0_eft_janus_z4_official_planck_lowlevel_gate import run_likelihood as run_lowlevel


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_emode_projection_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_emode_projection_scan.json")


def _write_spectra(scale: float) -> None:
    rows = assemble_spectra(e_mode_projection_scale=scale)
    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def score_scale(scale: float, execute_official: bool = True) -> dict:
    _write_spectra(scale)
    row = {
        "e_mode_projection_scale": scale,
        "official_executed": execute_official,
        "lowe_chi2": None,
        "highl_ttteee_chi2": None,
        "finite": True,
    }
    if execute_official:
        lowe = run_lowlevel("planck_2018_lowl.EE")
        highl = run_highl("planck_2018_highl_plik.TTTEEE")
        row["lowe_chi2"] = lowe["chi2"]
        row["highl_ttteee_chi2"] = highl["chi2"]
        row["finite"] = bool(lowe["finite"] and highl["finite"])
    return row


def _score_value(row: dict) -> float:
    values = [row.get("lowe_chi2"), row.get("highl_ttteee_chi2")]
    finite = [float(value) for value in values if value is not None and math.isfinite(float(value))]
    return sum(finite) if finite else math.inf


def build_payload(scales: tuple[float, ...] = (0.4, 0.7, 1.0, 1.3, 1.6), execute_official: bool = True) -> dict:
    rows: list[dict] = []
    try:
        for scale in scales:
            rows.append(score_scale(scale, execute_official=execute_official))
    finally:
        _write_spectra(1.0)
    best = min(rows, key=_score_value) if rows else None
    active = next((row for row in rows if row["e_mode_projection_scale"] == 1.0), None)
    best_is_active = bool(best and active and best["e_mode_projection_scale"] == active["e_mode_projection_scale"])
    return {
        "status": "janus-z4-emode-projection-scan",
        "native_z4_solver_used": True,
        "compressed_lcdm_parameters_used": False,
        "official_planck_likelihood_executed": execute_official,
        "rows": rows,
        "best": best,
        "active_scale_restored": True,
        "active_scale": 1.0,
        "best_is_active_scale": best_is_active,
        "emode_projection_scan_ready": True,
        "verdict": (
            "The spin-2 E-mode projection scale is now isolated as a diagnostic. "
            "If no scanned scale materially changes the official gates, the blocker "
            "is phase/source hierarchy rather than a single E-mode normalization."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 E-mode Projection Scan",
        "",
        f"Status: `{payload['status']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Active scale restored: `{payload['active_scale_restored']}`",
        f"Best is active scale: `{payload['best_is_active_scale']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        lines.append(
            f"- scale `{row['e_mode_projection_scale']}`: lowE `{row['lowe_chi2']}`, "
            f"highl TTTEEE `{row['highl_ttteee_chi2']}`, finite `{row['finite']}`"
        )
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
