from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_minimal_nonrustine_extension_contract import build_payload as build_contract
from scripts.build_p0_zero_axiom_closure_decision_gate import build_payload as build_decision


REPORT_PATH = Path("outputs/reports/p0_remaining_research_priority_queue.md")
JSON_PATH = Path("outputs/reports/p0_remaining_research_priority_queue.json")


def build_payload() -> dict:
    decision = build_decision()
    contract = build_contract()
    priorities = [
        {
            "priority": 1,
            "task": "derive_path_rule_from_action_or_noether",
            "success": "accepted Janus action supplies a covariant path family for same-L holonomy",
            "fallback": "current action/Noether attempt remains obstructed",
        },
        {
            "priority": 2,
            "task": "derive_source_stf_operator",
            "success": "accepted STF source/action chain closes",
            "fallback": "current partial STF no-go leaves only source-derived escape",
        },
        {
            "priority": 3,
            "task": "formalize_extension_contract_if_needed",
            "success": "explicit covariant extension candidate passes anti-rustine gates",
            "fallback": "no prediction claim",
        },
    ]
    return {
        "description": "Priority queue after current zero-axiom decision gate.",
        "status": "remaining-research-priority-queue-active",
        "decision_status": decision["status"],
        "contract_status": contract["status"],
        "priorities": priorities,
        "priority_count": len(priorities),
        "zero_axiom_closure_available": bool(decision["zero_axiom_closure_available"]),
        "new_axiom_adopted": False,
        "prediction_ready": False,
        "verdict": (
            "Work should now focus on source derivation or no-go completion. The "
            "extension contract is prepared only as a guardrail, not as an adopted model."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Remaining Research Priority Queue",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Priority count: {payload['priority_count']}",
        f"Zero-axiom closure available: {payload['zero_axiom_closure_available']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| priority | task | success | fallback |",
        "|---:|---|---|---|",
    ]
    for row in payload["priorities"]:
        lines.append(
            f"| {row['priority']} | {row['task']} | {row['success']} | "
            f"{row['fallback']} |"
        )
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
