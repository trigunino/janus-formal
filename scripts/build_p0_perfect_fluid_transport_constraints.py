from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_perfect_fluid_transport_constraints.md")
JSON_PATH = Path("outputs/reports/p0_perfect_fluid_transport_constraints.json")


def build_payload() -> dict:
    stress_forms = [
        "dust: K^{AB}=rho u^A u^B",
        "perfect fluid: K^{AB}=(rho+p)u^A u^B+p eta^{AB}",
        "projector form: K^{AB}=rho u^A u^B+p h^{AB}, h^{AB}=eta^{AB}+u^A u^B",
    ]
    added_constraints = [
        {
            "term": "pressure_gradient",
            "constrains": "receiver-frame Euler force through h^{AB}D_B p",
            "effect_on_f": "adds isotropic rest-space force constraints absent in dust",
        },
        {
            "term": "projector_derivative",
            "constrains": "D h^{AB}=D(u^A u^B) and therefore boost/acceleration parts of Omega",
            "effect_on_f": "does not constrain pure rest-space rotations because h is rotation-invariant",
        },
        {
            "term": "equation_of_state",
            "constrains": "cross pressure p_cross=w_cross rho_cross",
            "effect_on_f": "fixes scalar pressure-density closure only if w_cross is source-derived",
        },
    ]
    still_free_components = [
        "pure spatial rotation of an isotropic perfect-fluid rest frame",
        "screen-plane rotations invisible to rho, p and h",
        "anisotropic/shear transport not represented by p eta^{AB}",
    ]
    closure_upgrade = [
        "perfect fluid can improve dust by adding pressure-gradient and projector constraints",
        "perfect fluid still cannot determine full L/F because isotropic pressure is rotation-invariant",
        "anisotropic stress Pi^{AB} is required to constrain screen/rest-space orientation physically",
    ]
    forbidden_shortcuts = [
        "do not choose w_cross by fitting observations",
        "do not absorb pressure terms into scalar Q_det",
        "do not absorb pressure projection into scalar Q_cross",
        "do not claim full tensor transport from FLRW scalar perfect-fluid closure",
    ]
    return {
        "description": "P0 constraints added by perfect-fluid tensor transport beyond dust.",
        "status": "perfect-fluid-constraints-open",
        "pressure_constraints_added": True,
        "projector_constraints_added": True,
        "source_derived_w_cross": False,
        "pure_rotation_fixed": False,
        "full_l_transport_fixed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "stress_forms": stress_forms,
        "added_constraints": added_constraints,
        "still_free_components": still_free_components,
        "closure_upgrade": closure_upgrade,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "Perfect-fluid transport adds real tensor constraints beyond dust, but "
            "isotropic pressure cannot fix rest-space rotations. Full transport still "
            "needs source-derived w_cross and, for screen orientation, anisotropic stress."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Perfect-Fluid Transport Constraints",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Pressure constraints added: {payload['pressure_constraints_added']}",
        f"Projector constraints added: {payload['projector_constraints_added']}",
        f"Source-derived w_cross: {payload['source_derived_w_cross']}",
        f"Pure rotation fixed: {payload['pure_rotation_fixed']}",
        f"Full L transport fixed: {payload['full_l_transport_fixed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Stress Forms",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["stress_forms"])
    lines.extend(["", "## Added Constraints", ""])
    for row in payload["added_constraints"]:
        lines.append(f"- {row['term']}: {row['constrains']}; {row['effect_on_f']}")
    lines.extend(["", "## Still Free Components", ""])
    lines.extend(f"- {item}" for item in payload["still_free_components"])
    lines.extend(["", "## Closure Upgrade", ""])
    lines.extend(f"- {item}" for item in payload["closure_upgrade"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
