from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_noncomoving_dust_pde_constraints.md")
JSON_PATH = Path("outputs/reports/p0_noncomoving_dust_pde_constraints.json")


def build_payload() -> dict:
    assumptions = [
        "dust stress only: K_plus^{AB}=rho_minus u_-to+^A u_-to+^B",
        "u_-to+^A=L_-+^A_B u_-^B with Lorentz-preserving L",
        "Omega_alpha=(D_alpha L)L^{-1} and Omega_{alpha AB}=-Omega_{alpha BA}",
        "B_4vol product-rule terms kept in S_plus=B_plus K_plus",
        "mirror branch for K_minus",
    ]
    plus_constraints = [
        {
            "name": "densitized_continuity",
            "equation": "D_plus_B(B_plus rho_minus u_-to+^B)=0",
            "f_contraction": "rho_minus B_plus (Omega_B)^B_C u_-to+^C plus D log B_plus and density-flow terms",
            "fixes": "trace/divergence contraction of Omega along transported dust flux",
        },
        {
            "name": "receiver_force",
            "equation": "u_-to+^B D_plus_B u_-to+^A=0",
            "f_contraction": "u_-to+^B (Omega_B)^A_C u_-to+^C plus connection/source-velocity conversion terms",
            "fixes": "boost/acceleration projection of Omega along u_-to+",
        },
    ]
    minus_constraints = [
        {
            "name": "densitized_continuity",
            "equation": "D_minus_B(B_minus rho_plus u_+to-^B)=0",
            "f_contraction": "rho_plus B_minus (Omega_B)^B_C u_+to-^C plus D log B_minus and density-flow terms",
            "fixes": "trace/divergence contraction of mirror Omega along transported dust flux",
        },
        {
            "name": "receiver_force",
            "equation": "u_+to-^B D_minus_B u_+to-^A=0",
            "f_contraction": "u_+to-^B (Omega_B)^A_C u_+to-^C plus connection/source-velocity conversion terms",
            "fixes": "mirror boost/acceleration projection of Omega along u_+to-",
        },
    ]
    closure_statement = [
        "If densitized_continuity and receiver_force hold in both sectors, the dust part of D(BK)=0 closes",
        "Lorentz antisymmetry keeps the same L admissible for Q_cross",
        "The equations constrain Omega contractions but leave transverse rotation/gauge components",
    ]
    still_open = [
        "explicit source-derived Omega field",
        "transverse Lorentz gauge uniqueness",
        "boundary/initial data for non-comoving perturbations",
        "pressure/projector/Pi extension",
        "proof that Q_cross normalization follows from the same Omega",
    ]
    return {
        "description": "Non-comoving dust constraints induced by the zero-divergence PDE when K is transported by L.",
        "status": "noncomoving-dust-constraints-open",
        "constraints_written": True,
        "dust_closes_conditionally": True,
        "unique_omega_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "assumptions": assumptions,
        "plus_constraints": plus_constraints,
        "minus_constraints": minus_constraints,
        "closure_statement": closure_statement,
        "still_open": still_open,
        "verdict": (
            "The non-comoving dust PDE reduces to transported densitized continuity "
            "plus receiver-force equations. This constrains F/Omega, but does not "
            "uniquely solve the Lorentz transport field."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Non-Comoving Dust PDE Constraints",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Constraints written: {payload['constraints_written']}",
        f"Dust closes conditionally: {payload['dust_closes_conditionally']}",
        f"Unique Omega found: {payload['unique_omega_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    for title, key in (("Plus Constraints", "plus_constraints"), ("Minus Constraints", "minus_constraints")):
        lines.extend(["", f"## {title}", ""])
        for row in payload[key]:
            lines.append(f"- {row['name']}: `{row['equation']}`")
            lines.append(f"  - F contraction: {row['f_contraction']}")
            lines.append(f"  - fixes: {row['fixes']}")
    lines.extend(["", "## Closure Statement", ""])
    lines.extend(f"- {item}" for item in payload["closure_statement"])
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
