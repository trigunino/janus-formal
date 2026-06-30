from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_popt_acceptance_criteria.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_popt_acceptance_criteria.json")


def build_payload() -> dict:
    criteria = [
        {
            "name": "geometric_only",
            "requirement": "P_opt uses only g_plus, g_minus, phi, L, and null/tetrad projectors",
            "status": "required",
        },
        {
            "name": "same_transport",
            "requirement": "P_opt uses the same L and distribution f_to as kinetic stress",
            "status": "required",
        },
        {
            "name": "single_sheet_limit",
            "requirement": "P_opt reproduces the pre-caustic Q_cross candidate for one sheet",
            "status": "required-not-proved",
        },
        {
            "name": "no_scalar_fit",
            "requirement": "no A_fit, alpha_s, or observational normalization multiplier",
            "status": "enforced",
        },
    ]
    rejected = [
        "any P_opt containing free scalar amplitudes",
        "any P_opt using a different L than stress transport",
        "any P_opt that folds Q_det volume factors into lensing strength",
        "any P_opt calibrated to observed lensing before closure",
    ]
    decision = {
        "acceptance_criteria_defined": True,
        "popt_constructed": False,
        "prediction_ready": False,
        "reason": (
            "The allowed optical projector is now sharply constrained, but not built. "
            "The next proof must construct P_opt from Janus metric/tetrad data and pass "
            "the single-sheet and same-transport tests."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_popt_acceptance_criteria",
        "status": "popt-criteria-defined-construction-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "criteria": criteria,
        "rejected": rejected,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg P_opt Acceptance Criteria",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Criteria",
    ]
    for row in payload["criteria"]:
        lines.append(f"- {row['name']}: {row['requirement']} (status={row['status']})")
    lines.extend(["", "## Rejected"])
    lines.extend(f"- {item}" for item in payload["rejected"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Acceptance criteria defined: {decision['acceptance_criteria_defined']}",
            f"P_opt constructed: {decision['popt_constructed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
