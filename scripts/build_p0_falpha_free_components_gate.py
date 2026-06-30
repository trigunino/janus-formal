from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_falpha_free_components_gate.md")
JSON_PATH = Path("outputs/reports/p0_falpha_free_components_gate.json")


def build_payload() -> dict:
    determined_by = [
        "Lorentz preservation: F^T eta + eta F=0",
        "line-of-flow receiver force contraction",
        "transported continuity trace contraction",
        "mirror inverse derivative convention",
        "same-L K/Q_cross compatibility",
    ]
    still_free = [
        "transverse Lorentz-generator components not seen by one dust flow",
        "gauge/rotation branch of the tetrad map",
        "off-flow derivatives of L",
        "pressure/Pi orientation transport",
    ]
    closure_requirements = [
        "source equation or gauge principle fixes all free F_alpha components",
        "mirror F_plus/F_minus follows from one inverse L",
        "free components do not re-enter Q_cross or R_plus/R_minus",
    ]
    return {
        "description": "Gate for free components left by the F_alpha=D L Lorentz-generator constraints.",
        "status": "falpha-free-components-open",
        "determined_by": determined_by,
        "still_free": still_free,
        "closure_requirements": closure_requirements,
        "necessary_constraints_written": True,
        "all_falpha_components_source_fixed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The existing F equations constrain only part of D L. Source geometry or a "
            "declared gauge principle must fix the transverse/free components before closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 F_alpha Free Components Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Necessary constraints written: {payload['necessary_constraints_written']}",
        f"All F_alpha components source-fixed: {payload['all_falpha_components_source_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Determined By",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["determined_by"])
    lines.extend(["", "## Still Free", ""])
    lines.extend(f"- {item}" for item in payload["still_free"])
    lines.extend(["", "## Closure Requirements", ""])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
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
