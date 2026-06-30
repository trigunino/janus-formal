from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_d_source_derived_stf_operator_escape_gate import (
    build_payload as build_escape,
)
from scripts.build_p0_route_d_stf_operator_construction_obstruction import (
    build_payload as build_obstruction,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_stf_no_go_closure_attempt.md")
JSON_PATH = Path("outputs/reports/p0_route_d_stf_no_go_closure_attempt.json")


def build_payload() -> dict:
    escape = build_escape()
    obstruction = build_obstruction()
    closure_rows = [
        {
            "family": "formal_stf_without_janus_action",
            "closed_no_go": True,
            "reason": "formal rank-2 structure without action provenance is a residual operator",
        },
        {
            "family": "determinant_or_trace_source",
            "closed_no_go": True,
            "reason": "trace data cannot source the STF channel",
        },
        {
            "family": "source_free_derivative_stf",
            "closed_no_go": True,
            "reason": "source-free/boundary-free PDE certificate excludes it as selector",
        },
        {
            "family": "matter_pi_tf_without_eos_or_kinetic",
            "closed_no_go": True,
            "reason": "Pi_TF requires EOS, kinetic hierarchy, or source action",
        },
        {
            "family": "accepted_janus_source_derived_stf_operator",
            "closed_no_go": False,
            "reason": "cannot exclude an operator not yet specified by source/action",
        },
    ]
    return {
        "description": (
            "Attempt to close the remaining Route D STF no-go. It closes all "
            "currently explicit non-source-derived STF families and isolates the "
            "only unclosed logical escape."
        ),
        "status": "stf-no-go-closure-attempt-partial",
        "escape_status": escape["status"],
        "obstruction_status": obstruction["status"],
        "closure_rows": closure_rows,
        "closed_family_count": sum(1 for row in closure_rows if row["closed_no_go"]),
        "open_family_count": sum(1 for row in closure_rows if not row["closed_no_go"]),
        "accepted_janus_derived_stf_operator_exists": bool(escape["accepted_operator_exists"]),
        "all_known_non_source_stf_families_excluded": True,
        "full_stf_no_go_proved": False,
        "logical_escape_remaining": "accepted_janus_source_derived_stf_operator",
        "new_axiom_adopted": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The STF no-go is partial but sharper: all known non-source-derived STF "
            "routes are excluded. A fully source-derived Janus STF operator remains "
            "logically open until specified or ruled out."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D STF No-Go Closure Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Closed family count: {payload['closed_family_count']}",
        f"Open family count: {payload['open_family_count']}",
        f"Accepted Janus-derived STF operator exists: {payload['accepted_janus_derived_stf_operator_exists']}",
        f"All known non-source STF families excluded: {payload['all_known_non_source_stf_families_excluded']}",
        f"Full STF no-go proved: {payload['full_stf_no_go_proved']}",
        f"Logical escape remaining: {payload['logical_escape_remaining']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| family | closed no-go | reason |",
        "|---|---:|---|",
    ]
    for row in payload["closure_rows"]:
        lines.append(f"| {row['family']} | {row['closed_no_go']} | {row['reason']} |")
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
