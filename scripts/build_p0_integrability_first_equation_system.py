from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_integrability_first_equation_system.md")
JSON_PATH = Path("outputs/reports/p0_integrability_first_equation_system.json")


def build_payload() -> dict:
    unknowns = [
        {"symbol": "phi", "role": "regular inverse map between sectors"},
        {"symbol": "L/F_alpha", "role": "Lorentz/tetrad map with connection-form data"},
        {"symbol": "u_to", "role": "target congruence four-velocity"},
        {"symbol": "B_4vol", "role": "four-volume density multiplier"},
    ]
    equations = [
        {
            "name": "continuity",
            "formula": "D_alpha(B_4vol rho u_to^alpha)=0",
            "role": "mass-current conservation for the transported dust image",
            "status": "equation-not-solved",
        },
        {
            "name": "curl_frobenius",
            "formula": "d(u_flat_to)=0, equivalently projected_vorticity[u_to]=0",
            "role": "integrability/Frobenius gate for the congruence",
            "status": "equation-not-solved",
        },
        {
            "name": "inverse_map",
            "formula": "phi o phi^{-1}=id and phi^{-1} o phi=id",
            "role": "blocks independent source/target map choices",
            "status": "constraint-not-solved",
        },
        {
            "name": "l_inverse_lorentz",
            "formula": "L^{-1}L=I, L L^{-1}=I, and L^T eta L=eta",
            "role": "keeps L an inverse Lorentz/tetrad map",
            "status": "constraint-not-solved",
        },
        {
            "name": "same_phi_l_cuu",
            "formula": "C(u_to,u_to) is built from the same phi and L/F_alpha",
            "role": "prevents a separate optical/source bridge",
            "status": "identity-required",
        },
        {
            "name": "b_determinant_inverse",
            "formula": "B_4vol(phi(x)) B_4vol^{-1}(x)=1 with determinant/J_phi convention fixed",
            "role": "locks the inverse volume measure convention",
            "status": "constraint-not-solved",
        },
        {
            "name": "caustic_exclusion",
            "formula": "det(d phi) != 0 on the working patch",
            "role": "excludes caustics unless a sheeted extension is declared",
            "status": "regularity-assumption",
        },
    ]
    count = {
        "unknown_blocks": len(unknowns),
        "equation_blocks": len(equations),
        "solves_equations": False,
        "proves_uniqueness": False,
        "requires_boundary_data": True,
        "requires_gauge_fixing": True,
    }
    limitations = [
        "Equations are stated as a calculable system, not solved.",
        "Uniqueness is not proved.",
        "Boundary or initial data are required.",
        "Gauge choices for phi and L/F_alpha are required.",
        "Prediction claim is false until existence, uniqueness, and regularity are proved.",
    ]
    return {
        "description": "Bounded P0 artifact turning the integrability-first route into calculable equations.",
        "status": "integrability-first-equation-system-open",
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "fit_to_observations": False,
        "regular_patch_toy_solver_available": True,
        "unknowns": unknowns,
        "equations": equations,
        "count": count,
        "limitations": limitations,
        "verdict": (
            "This artifact makes the integrability-first route calculable by listing "
            "unknown fields and equation blocks. It does not solve the system, prove "
            "uniqueness, or justify predictions without boundary data, gauge fixing, "
            "and caustic control."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Integrability-First Equation System",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        f"Fit to observations: {payload['fit_to_observations']}",
        f"Regular patch toy solver available: {payload['regular_patch_toy_solver_available']}",
        "",
        "## Unknowns",
        "",
    ]
    lines.extend(f"- `{row['symbol']}`: {row['role']}" for row in payload["unknowns"])
    lines.extend(["", "## Equations", ""])
    for row in payload["equations"]:
        lines.append(f"- {row['name']}: `{row['formula']}` (status={row['status']})")
        lines.append(f"  - role: {row['role']}")
    count = payload["count"]
    lines.extend(
        [
            "",
            "## Count/Claim Gate",
            "",
            f"Unknown blocks: {count['unknown_blocks']}",
            f"Equation blocks: {count['equation_blocks']}",
            f"Solves equations: {count['solves_equations']}",
            f"Proves uniqueness: {count['proves_uniqueness']}",
            f"Requires boundary data: {count['requires_boundary_data']}",
            f"Requires gauge fixing: {count['requires_gauge_fixing']}",
            "",
            "## Limitations",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["limitations"])
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
