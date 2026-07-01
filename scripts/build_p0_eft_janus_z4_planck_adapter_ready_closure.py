from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.build_p0_eft_janus_z4_planck_likelihood_dry_run_target import write_reports as write_dry_run


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_adapter_ready_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_adapter_ready_closure.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_assembled_cmb_spectra.csv")
DRY_RUN_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_dry_run_target.json")


def build_payload() -> dict:
    dry_payload = write_dry_run()
    with SPECTRA_PATH.open(encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    required = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]
    columns_ready = bool(rows) and all(col in rows[0] for col in required)
    ell_values = [float(row["ell"]) for row in rows]
    ell_ready = all(b > a for a, b in zip(ell_values, ell_values[1:]))
    spectra_finite = all(
        math.isfinite(float(row[col]))
        for row in rows
        for col in required
    )

    return {
        "status": "janus-z4-planck-adapter-ready-closure",
        "spectra_path": str(SPECTRA_PATH),
        "dry_run_path": str(DRY_RUN_PATH),
        "spectrum_columns_ready": columns_ready,
        "ell_grid_ready": ell_ready,
        "spectra_finite": spectra_finite,
        "covariance_contract_ready": dry_payload["covariance_diagonal_positive"],
        "dry_run_chi2_finite": dry_payload["finite_chi2_produced"],
        "official_planck_likelihood_executed": False,
        "planck_likelihood_adapter_ready": (
            columns_ready
            and ell_ready
            and spectra_finite
            and dry_payload["covariance_diagonal_positive"]
            and dry_payload["finite_chi2_produced"]
        ),
        "scope": "Adapter is solver-ready; official Planck likelihood execution is not claimed.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Adapter Ready Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Spectrum columns ready: `{payload['spectrum_columns_ready']}`",
        f"Ell grid ready: `{payload['ell_grid_ready']}`",
        f"Spectra finite: `{payload['spectra_finite']}`",
        f"Dry-run chi2 finite: `{payload['dry_run_chi2_finite']}`",
        f"Planck likelihood adapter ready: `{payload['planck_likelihood_adapter_ready']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        "",
        payload["scope"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
