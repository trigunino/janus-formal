from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_loop_double_dual_conditional.md")
JSON_PATH = Path("outputs/reports/p0_eft_loop_double_dual_conditional.json")


def build_payload() -> dict:
    obligations = [
        {
            "id": "E1",
            "statement": "bulk modes are integrated out to produce a Wilsonian effective action",
            "proved": False,
        },
        {
            "id": "E2",
            "statement": "heat-kernel expansion generates curvature-radion operators",
            "proved": False,
        },
        {
            "id": "E3",
            "statement": "Janus/orbifold symmetry and degeneracy project out non-Horndeski terms",
            "proved": False,
        },
        {
            "id": "E4",
            "statement": "the double-dual coefficient is generated and stable under renormalization",
            "proved": False,
        },
    ]
    chain = [
        "bulk loop effective action",
        "heat-kernel curvature-radion tower",
        "orbifold/no-ghost projection to Horndeski/double-dual",
        "double-dual Cartan source",
        "Horndeski boundary completion",
        "dS scalar stability",
    ]
    theorem_status = {
        "eft_route_encoded": True,
        "heat_kernel_calculation_done": False,
        "conditional_closure_proved_if_obligations_hold": True,
        "unconditional_janus_closure_proved": False,
        "new_classical_rustine": False,
        "quantum_eft_obligation": True,
        "prediction_ready": False,
    }
    return {
        "description": "Conditional EFT/loop route that can source the double-dual Cartan term without a classical hand insertion.",
        "status": "eft-loop-route-encoded-open-heat-kernel",
        "theorem_status": theorem_status,
        "obligations": obligations,
        "chain": chain,
        "lean_module": "JanusFormal.Legacy.P0EFT.Gates.P0EFTLoopDoubleDualConditional",
        "verdict": (
            "This is the best non-classical no-rustine route: the double-dual term is treated "
            "as the local Wilsonian remnant of bulk loops. It remains conditional until the "
            "heat-kernel/projection calculation is actually derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    status = payload["theorem_status"]
    lines = [
        "# P0 EFT Loop Double-Dual Conditional Route",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in status.items())
    lines.extend(["", "## Obligations"])
    for row in payload["obligations"]:
        lines.append(f"- {row['id']}: {row['statement']} (proved={row['proved']})")
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
