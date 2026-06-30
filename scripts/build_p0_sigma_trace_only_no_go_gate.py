from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_sigma_trace_only_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_sigma_trace_only_no_go_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank = dimension * (dimension + 1) // 2
    trace_rank = 1
    trace_free_rank = symmetric_rank - trace_rank
    return {
        "description": "No-go gate: determinant/B4vol trace data cannot select full Sigma_alpha/D_alpha H.",
        "status": "trace-only-no-go-closed",
        "dimension": dimension,
        "rank_count": {
            "eta_symmetric_sigma_rank": symmetric_rank,
            "determinant_trace_rank": trace_rank,
            "trace_free_sigma_rank": trace_free_rank,
        },
        "trace_identity": "D_alpha log det(H)=Tr(H^{-1}D_alpha H)",
        "missing_channel": "trace-free N_alpha_TF / Q_TF has 9 components in 4D",
        "consequence": (
            "Any B4vol/Q_det/determinant-only source can at most constrain the scalar "
            "trace of the strain channel, not the anisotropic relative strain."
        ),
        "trace_only_selects_full_sigma": False,
        "trace_only_selects_qtf": False,
        "no_go_closed": True,
        "prediction_ready": False,
        "guardrails": [
            "do not promote determinant closure to tensor strain closure",
            "do not absorb Q_TF into Q_det or B4vol",
            "do not use trace-only data as a lensing tensor normalization",
        ],
        "remaining_lock": (
            "A source must independently select the trace-free strain/nonmetricity channel."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Sigma Trace-Only No-Go Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Trace-only selects full Sigma: {payload['trace_only_selects_full_sigma']}",
        f"Trace-only selects Q_TF: {payload['trace_only_selects_qtf']}",
        f"No-go closed: {payload['no_go_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Count",
        "",
    ]
    for key, value in payload["rank_count"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Trace Identity",
            "",
            f"`{payload['trace_identity']}`",
            "",
            f"Missing channel: {payload['missing_channel']}",
            "",
            f"Consequence: {payload['consequence']}",
            "",
            "## Guardrails",
            "",
        ]
    )
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
