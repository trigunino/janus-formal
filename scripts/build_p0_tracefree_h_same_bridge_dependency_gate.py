from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_same_bridge_dependency_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_same_bridge_dependency_gate.json")


def build_payload() -> dict:
    obligations = [
        {
            "obligation": "bridge_map",
            "requires": "explicit map placing Q_TF and X_TF on the same bridge branch",
            "closed": False,
        },
        {
            "obligation": "tetrad_L",
            "requires": "same tetrad/L used to define, pull back, and vary Q_TF and X_TF",
            "closed": False,
        },
        {
            "obligation": "projector_congruence_u",
            "requires": "same STF projector and congruence u for both tensors",
            "closed": False,
        },
        {
            "obligation": "measure",
            "requires": "same integration measure and density convention in the coupling",
            "closed": False,
        },
        {
            "obligation": "gauge_boundary",
            "requires": "gauge and boundary terms fixed before accepting the variation",
            "closed": False,
        },
        {
            "obligation": "dependency_variation",
            "requires": "include delta X_TF terms from H, L, phi, and matter dependencies",
            "closed": False,
        },
        {
            "obligation": "source_provenance",
            "requires": "X_TF source derived from accepted Janus equations/action",
            "closed": False,
        },
    ]
    dependency_terms = [
        {
            "dependency": "H",
            "variation_term": "int Q_TF^{ab} (delta X_TF_ab / delta H_cd) delta H_cd",
            "required_if_present": True,
        },
        {
            "dependency": "L",
            "variation_term": "int Q_TF^{ab} (delta X_TF_ab / delta L^c_d) delta L^c_d",
            "required_if_present": True,
        },
        {
            "dependency": "phi",
            "variation_term": "int Q_TF^{ab} (delta X_TF_ab / delta phi^c) delta phi^c",
            "required_if_present": True,
        },
        {
            "dependency": "matter",
            "variation_term": "int Q_TF^{ab} delta_matter X_TF_ab",
            "required_if_present": True,
        },
    ]
    rejected_routes = [
        {
            "route": "fixed_X_TF_by_hand",
            "allowed": False,
            "reason": "X_TF cannot be held fixed when it depends on H, L, phi, or matter",
        },
        {
            "route": "residual_source",
            "allowed": False,
            "reason": "a residual cancellation tensor is not source provenance",
        },
        {
            "route": "two_d_screen_as_4d_source",
            "allowed": False,
            "reason": "2D screen STF data is not automatically a 4D bridge source",
        },
        {
            "route": "scalar_trace",
            "allowed": False,
            "reason": "scalar trace data cannot source a trace-free rank-2 coupling",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for same-bridge and dependency obligations in a "
            "Q_TF X_TF linear coupling."
        ),
        "status": "tracefree-h-same-bridge-dependency-gate-open",
        "linear_coupling": "int Q_TF^{ab} X_TF_ab",
        "same_bridge_rule": (
            "The coupling is invalid unless Q_TF and X_TF live in the same "
            "bridge, tetrad, and congruence."
        ),
        "variation_rule": (
            "delta S includes int delta Q_TF^{ab} X_TF_ab plus int Q_TF^{ab} "
            "delta X_TF_ab; expand delta X_TF over H, L, phi, and matter "
            "dependencies when present."
        ),
        "obligations": obligations,
        "dependency_terms": dependency_terms,
        "rejected_routes": rejected_routes,
        "obligations_closed": sum(1 for row in obligations if row["closed"]),
        "obligations_total": len(obligations),
        "same_bridge_required": True,
        "same_tetrad_required": True,
        "same_congruence_required": True,
        "coupling_valid_without_same_bridge": False,
        "dependency_terms_required_if_present": True,
        "xtf_fixed_by_hand_allowed": False,
        "residual_source_allowed": False,
        "two_d_screen_as_4d_source_allowed": False,
        "scalar_trace_allowed": False,
        "source_provenance_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The Q_TF X_TF linear coupling is not admissible as a prediction "
            "input until same bridge/tetrad/congruence and dependency-variation "
            "obligations are closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Same-Bridge Dependency Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linear coupling: `{payload['linear_coupling']}`",
        f"Same-bridge rule: {payload['same_bridge_rule']}",
        f"Variation rule: {payload['variation_rule']}",
        f"Obligations closed: {payload['obligations_closed']}/{payload['obligations_total']}",
        f"Coupling valid without same bridge: {payload['coupling_valid_without_same_bridge']}",
        f"Dependency terms required if present: {payload['dependency_terms_required_if_present']}",
        f"X_TF fixed by hand allowed: {payload['xtf_fixed_by_hand_allowed']}",
        f"Residual source allowed: {payload['residual_source_allowed']}",
        f"2D screen as 4D source allowed: {payload['two_d_screen_as_4d_source_allowed']}",
        f"Scalar trace allowed: {payload['scalar_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Obligations",
        "",
        "| obligation | requires | closed |",
        "|---|---|---:|",
    ]
    for row in payload["obligations"]:
        lines.append(f"| {row['obligation']} | {row['requires']} | {row['closed']} |")
    lines.extend(
        [
            "",
            "## Dependency Terms",
            "",
            "| dependency | required if present | variation term |",
            "|---|---:|---|",
        ]
    )
    for row in payload["dependency_terms"]:
        lines.append(
            f"| {row['dependency']} | {row['required_if_present']} | "
            f"`{row['variation_term']}` |"
        )
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| route | allowed | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['route']} | {row['allowed']} | {row['reason']} |")
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
