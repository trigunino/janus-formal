from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_anisotropic_stress_orientation_constraints.md")
JSON_PATH = Path("outputs/reports/p0_anisotropic_stress_orientation_constraints.json")


def build_payload() -> dict:
    tensor_constraints = [
        "Pi^{AB}=Pi^{BA}",
        "eta_AB Pi^{AB}=0",
        "Pi^{AB}u_B=0",
        "transported Pi must preserve symmetry, trace-free condition, and orthogonality",
    ]
    orientation_role = [
        {
            "case": "Pi=0",
            "orientation_information": "none beyond isotropic rest frame",
            "effect_on_f": "rest-space rotations remain gauge/free",
        },
        {
            "case": "Pi has distinct spatial eigenvalues",
            "orientation_information": "principal axes define a physical screen/rest-space frame",
            "effect_on_f": "rotations that change Pi eigenvectors become observable and constrained",
        },
        {
            "case": "Pi has degenerate eigenvalues",
            "orientation_information": "only non-degenerate eigenspaces are fixed",
            "effect_on_f": "rotations inside degenerate subspaces remain gauge/free",
        },
    ]
    transport_equations = [
        "K_plus^{AB}=(rho_-+p_-)u_-to+^A u_-to+^B+p_- eta^{AB}+Pi_-to+^{AB}",
        "Pi_-to+^{AB}=L_minus_to_plus^A_C L_minus_to_plus^B_D Pi_-^{CD}",
        "D_plus_B(B_plus K_plus^{AB})=0 must include D Pi_-to+^{AB}",
        "mirror equations define K_minus and Pi_+to- with L_plus_to_minus",
    ]
    f_constraints_from_pi = [
        "D(Pi_to) includes Omega Pi + Pi Omega^T terms",
        "nonzero nondegenerate Pi constrains rest-space rotation components of Omega",
        "Pi evolution law must be source-derived; otherwise Pi can be used to overfit orientation",
        "screen/lensing shear contractions must use the same transported Pi and L map",
    ]
    still_open = [
        "Janus source papers do not provide a general Pi evolution law",
        "negative-sector matter may be modeled as dust/protostellar gas, so physical Pi may be small or absent",
        "if Pi=0 or degenerate, it cannot fix all rotations",
        "pressure and Pi closure must still satisfy R_plus=0 and R_minus=0 with B gradients",
    ]
    return {
        "description": "P0 anisotropic-stress constraints on the residual orientation freedom of L/F.",
        "status": "anisotropic-orientation-target",
        "pi_can_fix_orientation_when_nondegenerate": True,
        "pi_evolution_source_derived": False,
        "full_rotation_fixed_generically": False,
        "physics_closed": False,
        "prediction_ready": False,
        "tensor_constraints": tensor_constraints,
        "orientation_role": orientation_role,
        "transport_equations": transport_equations,
        "f_constraints_from_pi": f_constraints_from_pi,
        "still_open": still_open,
        "verdict": (
            "Anisotropic stress is the first matter term that can physically constrain "
            "rest-space/screen orientation. It fixes rotations only when Pi has "
            "non-degenerate structure and its evolution is source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Anisotropic-Stress Orientation Constraints",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Pi can fix orientation when nondegenerate: {payload['pi_can_fix_orientation_when_nondegenerate']}",
        f"Pi evolution source-derived: {payload['pi_evolution_source_derived']}",
        f"Full rotation fixed generically: {payload['full_rotation_fixed_generically']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Tensor Constraints",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["tensor_constraints"])
    lines.extend(["", "## Orientation Role", ""])
    for row in payload["orientation_role"]:
        lines.append(
            f"- {row['case']}: {row['orientation_information']}; {row['effect_on_f']}"
        )
    lines.extend(["", "## Transport Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["transport_equations"])
    lines.extend(["", "## F Constraints From Pi", ""])
    lines.extend(f"- {item}" for item in payload["f_constraints_from_pi"])
    lines.extend(["", "## Still Open", ""])
    lines.extend(f"- {item}" for item in payload["still_open"])
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
