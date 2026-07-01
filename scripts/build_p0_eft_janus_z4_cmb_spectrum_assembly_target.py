from __future__ import annotations

from pathlib import Path
import csv
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_spectrum_assembly_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_spectrum_assembly_target.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_assembled_cmb_spectra.csv")
FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]


def build_payload() -> dict:
    SPECTRA_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = []
    for ell in range(2, 52):
        damping = math.exp(-ell / 1800.0)
        base = damping / (ell * (ell + 1.0))
        tt = 1.0e-9 * base
        te = 0.12e-9 * base
        ee = 0.03e-9 * base
        pp = 0.002e-9 / ((ell + 1.0) ** 2)
        rows.append({"ell": ell, "cl_tt": tt, "cl_te": te, "cl_ee": ee, "cl_pp": pp})

    with SPECTRA_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)

    finite = all(math.isfinite(float(row[field])) for row in rows for field in FIELDS)
    monotone = all(rows[idx]["ell"] < rows[idx + 1]["ell"] for idx in range(len(rows) - 1))
    positive_auto = all(row["cl_tt"] > 0.0 and row["cl_ee"] > 0.0 and row["cl_pp"] > 0.0 for row in rows)
    return {
        "status": "janus-z4-cmb-spectrum-assembly-target",
        "spectra_path": str(SPECTRA_PATH),
        "row_count": len(rows),
        "ell_grid_strictly_increasing": monotone,
        "spectra_finite": finite,
        "positive_auto_spectra": positive_auto,
        "tt_spectrum_assembled": True,
        "te_spectrum_assembled": True,
        "ee_spectrum_assembled": True,
        "pp_spectrum_assembled": True,
        "spectra_finite_and_exportable": finite and monotone and positive_auto,
        "physical_transfer_functions_used": False,
        "planck_likelihood_adapter_ready": False,
        "next_required": "Replace analytic proxy spectra with physical Z4 transfer-function spectra and run Planck likelihood.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 CMB Spectrum Assembly Target",
        "",
        f"Status: `{payload['status']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Rows: `{payload['row_count']}`",
        f"Spectra finite/exportable: `{payload['spectra_finite_and_exportable']}`",
        f"Physical transfer functions used: `{payload['physical_transfer_functions_used']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
