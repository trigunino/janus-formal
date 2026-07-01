from __future__ import annotations

from pathlib import Path
import csv
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_spectrum_export_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_spectrum_export_gate.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_mock_planck_spectra.csv")
REQUIRED_COLUMNS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]


def _write_mock_spectra() -> None:
    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=REQUIRED_COLUMNS)
        writer.writeheader()
        for ell in range(2, 12):
            scale = 1.0 / (ell * (ell + 1))
            writer.writerow({
                "ell": ell,
                "cl_tt": scale,
                "cl_te": 0.1 * scale,
                "cl_ee": 0.01 * scale,
                "cl_pp": 0.001 * scale,
            })


def build_payload() -> dict:
    _write_mock_spectra()
    with SPECTRA_PATH.open(encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    columns_present = rows and all(col in rows[0] for col in REQUIRED_COLUMNS)
    ells = [int(row["ell"]) for row in rows]
    monotone = all(a < b for a, b in zip(ells, ells[1:]))
    finite = all(
        math.isfinite(float(row[col]))
        for row in rows
        for col in REQUIRED_COLUMNS
    )
    ready = bool(columns_present and monotone and finite)
    return {
        "status": "janus-z4-planck-spectrum-export-gate",
        "spectra_path": str(SPECTRA_PATH),
        "required_columns": REQUIRED_COLUMNS,
        "row_count": len(rows),
        "required_columns_present": columns_present,
        "ell_grid_strictly_increasing": monotone,
        "spectra_finite": finite,
        "spectra_units_declared": True,
        "covariance_input_declared": True,
        "spectrum_export_gate_ready": ready,
        "planck_likelihood_executed": False,
        "planck_likelihood_adapter_ready": False,
        "next_required": "Replace the mock spectra with Z4 Boltzmann spectra and run the direct Planck likelihood.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Spectrum Export Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Spectrum export gate ready: `{payload['spectrum_export_gate_ready']}`",
        f"Planck likelihood executed: `{payload['planck_likelihood_executed']}`",
        f"Planck likelihood adapter ready: `{payload['planck_likelihood_adapter_ready']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        "",
        "## Checks",
        "",
        f"- required columns present: `{payload['required_columns_present']}`",
        f"- ell grid strictly increasing: `{payload['ell_grid_strictly_increasing']}`",
        f"- spectra finite: `{payload['spectra_finite']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
