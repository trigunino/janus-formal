from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_projector_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_projector_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_h_components = dimension * (dimension + 1) // 2
    determinant_trace_rank = 1
    tracefree_rank = symmetric_h_components - determinant_trace_rank

    return {
        "description": "Bounded P0 gate for the trace-free H/Q_TF projector.",
        "status": "tracefree-h-projector-defined-not-source-closed",
        "dimension": dimension,
        "component_count": {
            "symmetric_h_components": symmetric_h_components,
            "determinant_trace_rank": determinant_trace_rank,
            "tracefree_h_rank": tracefree_rank,
        },
        "linearized_identity_branch": "P_TF(S)=S-(Tr(S)/4)I",
        "covariant_h_branch": "P_TF(N)=N-(Tr(H^{-1}N)/4)H",
        "trace_tests": [
            "Tr(P_TF(S))=0",
            "Tr(H^{-1}P_TF(N))=0",
        ],
        "determinant_trace_identity": "delta log det(H)=Tr(H^{-1} delta H)",
        "qtf_channel": "Q_TF / trace-free H strain has rank 9 in 4D",
        "scalar_trace_selects_qtf": False,
        "rejected_full_sources": [
            "scalar determinant",
            "B4vol",
            "Q_det",
        ],
        "projector_defined": True,
        "scalar_determinant_is_full_source": False,
        "b4vol_is_full_source": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not treat determinant trace as the full symmetric H source",
            "do not promote B4vol/Q_det to a Q_TF selector",
            "do not close predictions from trace-only data",
        ],
        "remaining_lock": (
            "Find an independent source/action selector for the rank-9 trace-free "
            "H/Q_TF channel."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Projector Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Projector defined: {payload['projector_defined']}",
        f"Scalar trace selects Q_TF: {payload['scalar_trace_selects_qtf']}",
        f"Scalar determinant is full source: {payload['scalar_determinant_is_full_source']}",
        f"B4vol is full source: {payload['b4vol_is_full_source']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Component Count",
        "",
    ]
    for key, value in payload["component_count"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Projectors",
            "",
            f"- linearized identity branch: `{payload['linearized_identity_branch']}`",
            f"- covariant H branch: `{payload['covariant_h_branch']}`",
            "",
            "## Trace Tests",
            "",
        ]
    )
    lines.extend(f"- `{item}`" for item in payload["trace_tests"])
    lines.extend(
        [
            "",
            "## Determinant Boundary",
            "",
            f"- determinant trace identity: `{payload['determinant_trace_identity']}`",
            f"- Q_TF channel: {payload['qtf_channel']}",
            "",
            "Rejected full sources:",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["rejected_full_sources"])
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
    lines.extend(["", f"Remaining lock: {payload['remaining_lock']}", ""])
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
