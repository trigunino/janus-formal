from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sheet_sum_dust_model.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sheet_sum_dust_model.json")


def build_payload() -> dict:
    sheet_model = [
        {
            "object": "stress_sum",
            "formula": "T_to^{mu nu} = sum_s rho_s_to u_s_to^mu u_s_to^nu",
            "rule": "each sheet s has its own transported density and velocity",
        },
        {
            "object": "map_sum",
            "formula": "phi = {phi_s}_s as a finite set of single-valued sheet maps",
            "rule": "post-caustic relation is multi-map, not one diffeomorphism",
        },
        {
            "object": "residual_sum",
            "formula": "h div T_to = sum_s rho_s_to h_s C_s u_s u_s",
            "rule": "closure is sheet-wise before summation",
        },
        {
            "object": "optical_sum",
            "formula": "Q_cross_total = sum_s Q_cross[phi_s,L_s,rho_s]",
            "rule": "no independent Q_cross amplitude per sheet",
        },
    ]
    obligations = [
        "sheet weights are transported density-volume weights",
        "each sheet has inverse mirror support or is excluded from mirror closure",
        "same-L rule applies on every sheet",
        "sheet creation at caustic must conserve total transported mass",
        "finite sheet truncation must be a numerical diagnostic, not a physical fit",
    ]
    decision = {
        "post_caustic_route_defined": True,
        "single_diffeomorphism_replaced": True,
        "new_fit_parameters": False,
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The sheet-sum model gives a non-fit post-caustic route: replace one map by "
            "a finite family of single-valued maps and sum their transported stresses. "
            "It is not closed until sheet creation, mirror support, and optical summation "
            "are derived consistently."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_sheet_sum_dust_model",
        "status": "sheet-sum-model-defined-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "sheet_model": sheet_model,
        "closure_obligations": obligations,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Sheet-Sum Dust Model",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Sheet Model",
    ]
    for row in payload["sheet_model"]:
        lines.append(f"- {row['object']}: `{row['formula']}`")
        lines.append(f"  - rule: {row['rule']}")
    lines.extend(["", "## Closure Obligations"])
    lines.extend(f"- {item}" for item in payload["closure_obligations"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Post-caustic route defined: {decision['post_caustic_route_defined']}",
            f"Single diffeomorphism replaced: {decision['single_diffeomorphism_replaced']}",
            f"New fit parameters: {decision['new_fit_parameters']}",
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
