from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.build_p0_eft_janus_z4_cmb_spectrum_assembly_target import write_reports as write_spectra


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_dry_run_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_dry_run_target.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_assembled_cmb_spectra.csv")


def build_payload() -> dict:
    if not SPECTRA_PATH.exists():
        write_spectra()
    with SPECTRA_PATH.open(encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    chi2 = 0.0
    dof = 0
    max_pull = 0.0
    for row in rows:
        ell = float(row["ell"])
        for col, target_scale in (("cl_tt", 1.01), ("cl_te", 0.99), ("cl_ee", 1.02), ("cl_pp", 0.98)):
            model = float(row[col])
            target = target_scale * model
            sigma = max(abs(model) * 0.05, 1.0e-20) * (1.0 + 0.001 * ell)
            pull = (model - target) / sigma
            chi2 += pull * pull
            dof += 1
            max_pull = max(max_pull, abs(pull))

    finite = math.isfinite(chi2) and math.isfinite(max_pull) and dof > 0
    return {
        "status": "janus-z4-planck-likelihood-dry-run-target",
        "spectra_path": str(SPECTRA_PATH),
        "dof": dof,
        "chi2": chi2,
        "chi2_per_dof": chi2 / dof if dof else None,
        "max_pull": max_pull,
        "residual_vector_declared": True,
        "covariance_diagonal_positive": True,
        "finite_chi2_produced": finite,
        "spectra_adapter_input_used": True,
        "dry_run_report_exported": True,
        "official_planck_likelihood_executed": False,
        "planck_likelihood_adapter_ready": False,
        "next_required": "Replace mock target/covariance with official Planck likelihood inputs and execute the real adapter.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Likelihood Dry Run Target",
        "",
        f"Status: `{payload['status']}`",
        f"chi2/dof: `{payload['chi2_per_dof']}`",
        f"max pull: `{payload['max_pull']}`",
        f"finite chi2: `{payload['finite_chi2_produced']}`",
        f"official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
