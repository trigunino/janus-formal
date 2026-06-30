from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_transport_f_equations.md")
JSON_PATH = Path("outputs/reports/p0_source_transport_f_equations.json")


def build_payload() -> dict:
    definitions = [
        "D_minus_alpha L_minus_to_plus^A_B = F_minus_to_plus^A_{B alpha}",
        "D_plus_alpha L_plus_to_minus^A_B = F_plus_to_minus^A_{B alpha}",
        "u_-to+^A=L_minus_to_plus^A_B u_-^B",
        "u_+to-^A=L_plus_to_minus^A_B u_+^B",
    ]
    lorentz_preservation = [
        "F_minus_to_plus^T eta L_minus_to_plus + L_minus_to_plus^T eta F_minus_to_plus = 0",
        "F_plus_to_minus^T eta L_plus_to_minus + L_plus_to_minus^T eta F_plus_to_minus = 0",
        "equivalently Omega_minus=(D L_minus_to_plus)L_minus_to_plus^{-1} is eta-antisymmetric",
        "equivalently Omega_plus=(D L_plus_to_minus)L_plus_to_minus^{-1} is eta-antisymmetric",
    ]
    plus_constraints = [
        {
            "name": "transported_continuity_plus",
            "equation": "D_minus_A(rho_minus u_-to+^A)=0",
            "expansion": "u_-to+^A D_minus_A rho_minus + rho_minus D_minus_A(L_minus_to_plus^A_B u_-^B)=0",
            "f_content": "rho_minus F_minus_to_plus^A_{B A} u_-^B plus ordinary derivative/connection pieces",
        },
        {
            "name": "receiver_force_plus",
            "equation": "u_-to+^B D_minus_B u_-to+^A + C^A_{BC}u_-to+^C u_-to+^B=0",
            "expansion": "u_-to+^B F_minus_to_plus^A_{D B}u_-^D + u_-to+^B L_minus_to_plus^A_D D_minus_B u_-^D + C^A_{BC}u_-to+^C u_-to+^B=0",
            "f_content": "line-of-flow contraction u_-to+^B F_minus_to_plus^A_{D B}u_-^D",
        },
    ]
    minus_constraints = [
        {
            "name": "transported_continuity_minus",
            "equation": "D_plus_A(rho_plus u_+to-^A)=0",
            "expansion": "u_+to-^A D_plus_A rho_plus + rho_plus D_plus_A(L_plus_to_minus^A_B u_+^B)=0",
            "f_content": "rho_plus F_plus_to_minus^A_{B A} u_+^B plus ordinary derivative/connection pieces",
        },
        {
            "name": "receiver_force_minus",
            "equation": "u_+to-^B D_plus_B u_+to-^A - C^A_{BC}u_+to-^C u_+to-^B=0",
            "expansion": "u_+to-^B F_plus_to_minus^A_{D B}u_+^D + u_+to-^B L_plus_to_minus^A_D D_plus_B u_+^D - C^A_{BC}u_+to-^C u_+to-^B=0",
            "f_content": "line-of-flow contraction u_+to-^B F_plus_to_minus^A_{D B}u_+^D",
        },
    ]
    density_measure_constraints = [
        "D_plus_A(B_plus K_plus^{AB}) must use the same B_plus as Q_det/proper-density mapping",
        "D_minus_A(B_minus K_minus^{AB}) must use the same B_minus as Q_det/proper-density mapping",
        "grad(log B_plus)K_plus and grad(log B_minus)K_minus cannot be dropped",
    ]
    minimal_closure_statement = [
        "If Lorentz preservation holds for F_minus/F_plus",
        "and transported continuity plus/minus constraints hold",
        "and receiver-force plus/minus constraints hold",
        "and density-measure constraints cancel B gradients",
        "then Lorentz-transported dust closes R_plus=0 and R_minus=0 conditionally",
    ]
    still_not_source_derived = [
        "the full tensor F_minus_to_plus is underdetermined by contractions along one flow",
        "the transverse/gauge part of F must be fixed by Janus geometry or a gauge convention",
        "accepted papers do not yet provide this F as an explicit source equation",
        "pressure and Pi require additional tensor transport constraints",
    ]
    return {
        "description": "Minimal equations that a source-derived F=D L must satisfy for Lorentz-dust closure.",
        "status": "f-equations-derived-as-constraints",
        "f_constraints_written": True,
        "lorentz_preservation_written": True,
        "plus_residual_constraints_written": True,
        "minus_residual_constraints_written": True,
        "density_measure_constraints_written": True,
        "source_derived_f_found": False,
        "r_plus_closed_conditionally": True,
        "r_minus_closed_conditionally": True,
        "physics_closed": False,
        "prediction_ready": False,
        "definitions": definitions,
        "lorentz_preservation": lorentz_preservation,
        "plus_constraints": plus_constraints,
        "minus_constraints": minus_constraints,
        "density_measure_constraints": density_measure_constraints,
        "minimal_closure_statement": minimal_closure_statement,
        "still_not_source_derived": still_not_source_derived,
        "verdict": (
            "We can derive the equations F must satisfy. They close the Lorentz-dust "
            "branch conditionally, but they do not uniquely determine F until Janus "
            "source geometry or gauge conditions fix its transverse components."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source Transport F Equations",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"F constraints written: {payload['f_constraints_written']}",
        f"Lorentz preservation written: {payload['lorentz_preservation_written']}",
        f"Source-derived F found: {payload['source_derived_f_found']}",
        f"R_plus closed conditionally: {payload['r_plus_closed_conditionally']}",
        f"R_minus closed conditionally: {payload['r_minus_closed_conditionally']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Definitions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["definitions"])
    lines.extend(["", "## Lorentz Preservation", ""])
    lines.extend(f"- `{item}`" for item in payload["lorentz_preservation"])
    lines.extend(["", "## Plus Constraints", ""])
    for row in payload["plus_constraints"]:
        lines.append(f"- {row['name']}: `{row['equation']}`")
        lines.append(f"  - expansion: `{row['expansion']}`")
        lines.append(f"  - F content: {row['f_content']}")
    lines.extend(["", "## Minus Constraints", ""])
    for row in payload["minus_constraints"]:
        lines.append(f"- {row['name']}: `{row['equation']}`")
        lines.append(f"  - expansion: `{row['expansion']}`")
        lines.append(f"  - F content: {row['f_content']}")
    lines.extend(["", "## Density Measure Constraints", ""])
    lines.extend(f"- {item}" for item in payload["density_measure_constraints"])
    lines.extend(["", "## Minimal Closure Statement", ""])
    lines.extend(f"- {item}" for item in payload["minimal_closure_statement"])
    lines.extend(["", "## Still Not Source-Derived", ""])
    lines.extend(f"- {item}" for item in payload["still_not_source_derived"])
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
