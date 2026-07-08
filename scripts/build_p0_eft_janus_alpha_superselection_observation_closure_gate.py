from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
FIT_JSON = REPORTS / "p0_eft_janus_z2_alpha_observational_fit_gate.json"
ENDPOINT_JSON = REPORTS / "p0_eft_janus_alpha_superselection_observation_endpoint_gate.json"
JSON_PATH = REPORTS / "p0_eft_janus_alpha_superselection_observation_closure_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_alpha_superselection_observation_closure_gate.md"


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def build_payload() -> dict[str, Any]:
    fit = _read(FIT_JSON)
    endpoint = _read(ENDPOINT_JSON)
    primary = (fit or {}).get("best_fit", {}).get("SN_full_cov_plus_BAO", {})
    q0 = primary.get("q0")
    boundary = bool(primary.get("at_grid_boundary")) if primary else False
    bao_status = (fit or {}).get("janus_bao_status")
    full_ready = bool((endpoint or {}).get("full_sector_selection_ready"))
    runner_executed = fit is not None and endpoint is not None and full_ready
    interior_selected = runner_executed and not boundary and bao_status != "rejected_in_current_background_proxy"
    return {
        "status": "janus-alpha-superselection-observation-closure",
        "inputs": {
            "fit_json": str(FIT_JSON),
            "endpoint_json": str(ENDPOINT_JSON),
            "fit_exists": fit is not None,
            "endpoint_exists": endpoint is not None,
        },
        "sn_bao_runner_executed": runner_executed,
        "primary_endpoint": "SN_full_cov_plus_BAO",
        "primary_q0": q0,
        "primary_u0": primary.get("u0"),
        "primary_chi2": primary.get("chi2"),
        "primary_at_grid_boundary": boundary,
        "bao_scale": primary.get("bao_scale"),
        "janus_bao_status": bao_status,
        "interior_janus_sector_selected": interior_selected,
        "classification": (
            "superselection_calibration_closes_negative_for_current_background_proxy"
            if runner_executed and boundary
            else "superselection_calibration_incomplete"
            if not runner_executed
            else "interior_sector_selected"
        ),
        "allowed_conclusion": (
            "With the current paper-native/background-proxy BAO map, SN+BAO selects the "
            "q0 -> 0- boundary rather than an interior Janus sector. This closes the "
            "alpha-superselection observational pass negatively for the current proxy."
        )
        if runner_executed and boundary
        else "Observation closure is not complete.",
        "next_if_reopened": [
            "derive a native Janus BAO/ruler contract instead of current proxy",
            "rerun SN+BAO with that native ruler",
            "only then reassess alpha-sector selection",
        ],
        "no_fit_claim_forbidden": True,
        "gate_passed": runner_executed,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Alpha Superselection Observation Closure",
        "",
        f"Runner executed: `{payload['sn_bao_runner_executed']}`",
        f"Classification: `{payload['classification']}`",
        f"Primary q0: `{payload['primary_q0']}`",
        f"At grid boundary: `{payload['primary_at_grid_boundary']}`",
        f"Janus BAO status: `{payload['janus_bao_status']}`",
        f"Interior Janus sector selected: `{payload['interior_janus_sector_selected']}`",
        "",
        "## Allowed Conclusion",
        "",
        payload["allowed_conclusion"],
        "",
        "## Reopen Only If",
        "",
        *[f"- {item}" for item in payload["next_if_reopened"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
