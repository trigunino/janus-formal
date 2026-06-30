from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_route_d_tensor_derivative_admissibility_filter.md")
JSON_PATH = Path("outputs/reports/p0_route_d_tensor_derivative_admissibility_filter.json")


def build_payload() -> dict:
    filter_rows = [
        {
            "candidate": "free_tracefree_tensor_source",
            "required_failure": "no Janus action/source provenance",
            "excluded": True,
        },
        {
            "candidate": "free_derivative_curvature_operator",
            "required_failure": "operator chosen as residual rather than source equation",
            "excluded": True,
        },
        {
            "candidate": "determinant_or_volume_trace_source",
            "required_failure": "trace object cannot source STF rank-2 channel",
            "excluded": True,
        },
        {
            "candidate": "source_covariant_stf_operator",
            "required_failure": "none yet; must pass all gates",
            "excluded": False,
        },
    ]
    admissibility_gates = [
        "operator is derived by varying an accepted Janus source/action",
        "Euler-Lagrange output has symmetric trace-free rank-2 channel",
        "split Noether identity leaves no unbalanced divergence residual",
        "same L transports K, Q_cross, and matter moments",
        "principal symbol passes ghost/tachyon/stability screen",
        "mirror plus/minus inverse condition is satisfied",
    ]
    return {
        "description": (
            "Route D filter for the surviving tensor/derivative families: exclude "
            "free residual tensors and keep only source-covariant STF operators "
            "that can pass provenance, Noether, same-L, mirror, and stability gates."
        ),
        "status": "tensor-derivative-admissibility-filter-open",
        "filter_rows": filter_rows,
        "admissibility_gates": admissibility_gates,
        "excluded_free_family_count": sum(1 for row in filter_rows if row["excluded"]),
        "open_conditional_family_count": sum(1 for row in filter_rows if not row["excluded"]),
        "free_tracefree_tensor_allowed": False,
        "free_derivative_operator_allowed": False,
        "source_covariant_stf_operator_open": True,
        "full_no_go_proved": False,
        "accepted_candidate_exists": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Route D is tighter: trace-free or derivative objects are not accepted "
            "just because they have the right tensor rank. Free residual tensors, "
            "free derivative operators, and trace/determinant sources are excluded. "
            "Only a Janus-derived covariant STF operator remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Tensor/Derivative Admissibility Filter",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Excluded free family count: {payload['excluded_free_family_count']}",
        f"Open conditional family count: {payload['open_conditional_family_count']}",
        f"Free tracefree tensor allowed: {payload['free_tracefree_tensor_allowed']}",
        f"Free derivative operator allowed: {payload['free_derivative_operator_allowed']}",
        f"Source-covariant STF operator open: {payload['source_covariant_stf_operator_open']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| candidate | required failure | excluded |",
        "|---|---|---:|",
    ]
    for row in payload["filter_rows"]:
        lines.append(f"| {row['candidate']} | {row['required_failure']} | {row['excluded']} |")
    lines.extend(["", "## Admissibility Gates", ""])
    lines.extend(f"- {item}" for item in payload["admissibility_gates"])
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
