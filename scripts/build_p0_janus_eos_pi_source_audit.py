from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_eos_pi_source_audit.md")
JSON_PATH = Path("outputs/reports/p0_janus_eos_pi_source_audit.json")


def build_payload() -> dict:
    source_rows = [
        {
            "source": "M15",
            "anchor": "rho(+)>0, p(+)>0; rho(-)<0, p(-)<0",
            "supports": "pressure sign convention",
            "does_not_supply": "equation of state p=w rho or Pi evolution",
        },
        {
            "source": "M30",
            "anchor": "coupled bimetric/geodesic source equations",
            "supports": "signed source slots and Newtonian limit",
            "does_not_supply": "general perfect-fluid EOS or anisotropic-stress transport",
        },
        {
            "source": "X2025-kinetic-galactic",
            "anchor": "Vlasov/Poisson construction for galaxy dynamics",
            "supports": "future kinetic closure route",
            "does_not_supply": "current tensor Bianchi pressure/Pi closure",
        },
    ]
    closure_routes = [
        {
            "route": "dust",
            "requirement": "explicitly assume p=0 and Pi=0",
            "status": "conditional",
        },
        {
            "route": "barotropic_perfect_fluid",
            "requirement": "derive or source-select w_cross",
            "status": "open",
        },
        {
            "route": "kinetic_moments",
            "requirement": "derive p and Pi from distribution-function moments and close hierarchy",
            "status": "open",
        },
        {
            "route": "pi_zero_proof",
            "requirement": "prove isotropy/eigenframe keeps Pi^{AB}=0 under transport",
            "status": "open",
        },
    ]
    return {
        "description": "Source audit for Janus equation-of-state and anisotropic-stress closure.",
        "status": "eos-pi-source-audit-open",
        "source_rows": source_rows,
        "closure_routes": closure_routes,
        "pressure_sign_source_verified": True,
        "equation_of_state_source_derived": False,
        "pi_evolution_source_derived": False,
        "pi_zero_source_proved": False,
        "kinetic_route_available_as_secondary_source": True,
        "dust_branch_only_conditional": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Accepted Janus sources provide pressure signs and source slots, not a general EOS or Pi law. "
            "The next non-rustine paths are explicit dust, source-selected EOS, kinetic moments, or a Pi=0 proof."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus EOS/Pi Source Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Pressure sign source verified: {payload['pressure_sign_source_verified']}",
        f"Equation of state source-derived: {payload['equation_of_state_source_derived']}",
        f"Pi evolution source-derived: {payload['pi_evolution_source_derived']}",
        f"Pi zero source proved: {payload['pi_zero_source_proved']}",
        f"Kinetic route available as secondary source: {payload['kinetic_route_available_as_secondary_source']}",
        f"Dust branch only conditional: {payload['dust_branch_only_conditional']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
        "| source | anchor | supports | does not supply |",
        "|---|---|---|---|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['source']} | `{row['anchor']}` | {row['supports']} | {row['does_not_supply']} |"
        )
    lines.extend(["", "## Closure Routes", "", "| route | requirement | status |", "|---|---|---|"])
    for row in payload["closure_routes"]:
        lines.append(f"| {row['route']} | {row['requirement']} | {row['status']} |")
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
