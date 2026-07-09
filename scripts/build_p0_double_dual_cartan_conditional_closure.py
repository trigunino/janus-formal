from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_double_dual_cartan_conditional_closure.md")
JSON_PATH = Path("outputs/reports/p0_double_dual_cartan_conditional_closure.json")


def build_payload() -> dict:
    assumptions = [
        {
            "id": "A_DoubleDualCartanSource",
            "statement": "Janus-Cartan action contains the orbifold-even parity-even double-dual curvature-torsion invariant",
            "source_derived_from_published_janus": False,
            "conditional_role": "generates the Horndeski-radion bulk coupling",
        },
        {
            "id": "A_HorndeskiBoundaryCompletion",
            "statement": "the Horndeski-radion variational principle includes its required boundary completion",
            "source_derived_from_published_janus": False,
            "conditional_role": "closes the k4 boundary contact",
        },
    ]
    chain = [
        "double-dual Cartan source",
        "Horndeski-radion bulk coupling",
        "Horndeski boundary completion",
        "k2 and k4 contact closure",
        "dS scalar alpha/beta/sound-speed stability",
    ]
    theorem_status = {
        "conditional_closure_proved": True,
        "unconditional_janus_closure_proved": False,
        "new_axiom": True,
        "no_observational_fit": True,
        "prediction_ready": False,
        "conditional_prediction_ready_path_open": True,
    }
    return {
        "description": "Conditional double-dual Cartan route from Janus-Cartan extension to dS scalar stability.",
        "status": "conditional-extension-not-published-janus",
        "theorem_status": theorem_status,
        "assumptions": assumptions,
        "chain": chain,
        "lean_module": "JanusFormal.Legacy.P0.Gates.P0DoubleDualCartanConditionalClosure",
        "verdict": (
            "This is the clean conditional route. It is not a hidden repair: "
            "A_DoubleDualCartanSource is explicit and remains the only non-published step."
        ),
    }


def render_markdown(payload: dict) -> str:
    status = payload["theorem_status"]
    lines = [
        "# P0 Double-Dual Cartan Conditional Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in status.items())
    lines.extend(["", "## Assumptions"])
    for row in payload["assumptions"]:
        lines.append(
            f"- {row['id']}: {row['statement']} "
            f"(source_derived_from_published_janus={row['source_derived_from_published_janus']})"
        )
    lines.extend(["", "## Chain"])
    lines.extend(f"- {item}" for item in payload["chain"])
    lines.extend(["", f"Lean module: `{payload['lean_module']}`", "", f"Verdict: {payload['verdict']}", ""])
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
