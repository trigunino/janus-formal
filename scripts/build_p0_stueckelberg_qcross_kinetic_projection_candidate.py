from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_qcross_kinetic_projection_candidate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_qcross_kinetic_projection_candidate.json")


def build_payload() -> dict:
    projection_forms = [
        {
            "name": "stress_moment_projection",
            "formula": "Q_cross = P_opt[g_plus,g_minus,L] : int p p f_to dP",
            "status": "candidate",
        },
        {
            "name": "sheet_limit",
            "formula": "Q_cross = sum_s P_opt[g_plus,g_minus,L_s] : (rho_s u_s u_s)",
            "status": "cold-limit-candidate",
        },
        {
            "name": "forbidden_scalar_amplitude",
            "formula": "Q_cross = A_fit sum_s Q_s",
            "status": "rejected",
        },
    ]
    closure_requirements = [
        "P_opt must be built from metric/tetrad/map data only",
        "same L used in stress transport appears in P_opt",
        "Q_det volume weights remain separate from optical projection",
        "projection must reproduce pre-caustic single-sheet Q_cross",
        "no observational normalization before residual gates close",
    ]
    decision = {
        "qcross_projection_shape_defined": True,
        "uses_same_distribution": True,
        "source_derived": False,
        "independent_amplitude_allowed": False,
        "prediction_ready": False,
        "reason": (
            "Q_cross can be constrained as an optical projection of the same kinetic "
            "stress moment used by matter transport. This is a no-fit candidate shape, "
            "not a derived Janus lensing law yet."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_qcross_kinetic_projection_candidate",
        "status": "qcross-kinetic-projection-candidate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "projection_forms": projection_forms,
        "closure_requirements": closure_requirements,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Q_cross Kinetic Projection Candidate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Projection Forms",
    ]
    for row in payload["projection_forms"]:
        lines.append(f"- {row['name']}: `{row['formula']}` (status={row['status']})")
    lines.extend(["", "## Closure Requirements"])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Q_cross projection shape defined: {decision['qcross_projection_shape_defined']}",
            f"Uses same distribution: {decision['uses_same_distribution']}",
            f"Source derived: {decision['source_derived']}",
            f"Independent amplitude allowed: {decision['independent_amplitude_allowed']}",
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
