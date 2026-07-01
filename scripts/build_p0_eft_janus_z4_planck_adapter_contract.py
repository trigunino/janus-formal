from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_adapter_contract.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_adapter_contract.json")


def build_payload() -> dict:
    required_columns = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]
    checks = {
        "tt_spectrum_export_declared": True,
        "te_spectrum_export_declared": True,
        "ee_spectrum_export_declared": True,
        "lensing_spectrum_export_declared": True,
        "ell_grid_and_units_declared": True,
        "covariance_or_likelihood_declared": True,
        "direct_planck_likelihood_executed": False,
    }
    return {
        "status": "janus-z4-planck-adapter-contract",
        "lean_module": "JanusFormal.P0EFTJanusZ4PlanckAdapterContract",
        "required_columns": required_columns,
        "unit_contract": "dimensionless C_ell arrays on Planck likelihood ell grid",
        "checks": checks,
        "adapter_contract_ready": all(value for key, value in checks.items() if key != "direct_planck_likelihood_executed"),
        "adapter_physical_ready": False,
        "next_required": "Run a direct Planck likelihood on non-proxy Z4 spectra.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Adapter Contract",
        "",
        f"Status: `{payload['status']}`",
        f"Required columns: `{', '.join(payload['required_columns'])}`",
        f"Unit contract: {payload['unit_contract']}",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", f"Adapter contract ready: `{payload['adapter_contract_ready']}`", f"Adapter physical ready: `{payload['adapter_physical_ready']}`", "", f"Next required: {payload['next_required']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
