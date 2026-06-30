from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_kinetic_closure_routes_decision.md")
JSON_PATH = Path("outputs/reports/p0_janus_kinetic_closure_routes_decision.json")


def build_payload() -> dict:
    routes = [
        {
            "route": "cold_dust",
            "closure_rule": "P_ij=0 and Q_ijk=0",
            "allowed": "conditional",
            "risk": "not general EOS/Pi physics",
        },
        {
            "route": "isotropic_dispersion",
            "closure_rule": "P_ij=p delta_ij and Pi_ij=0",
            "allowed": "open",
            "risk": "needs source-derived p(rho) and isotropy preservation",
        },
        {
            "route": "truncated_moment",
            "closure_rule": "Q_ijk=0",
            "allowed": "rejected_without_source",
            "risk": "uncontrolled heat-flux truncation is a hidden model assumption",
        },
        {
            "route": "full_vlasov",
            "closure_rule": "solve f with Janus geodesic/source flow, compute moments",
            "allowed": "target",
            "risk": "requires phase-space solver and source-derived cross-map",
        },
    ]
    next_work = [
        "use cold_dust only under p=Pi=0 contract",
        "derive isotropic_dispersion from a preserved isotropic f before setting Pi=0",
        "do not set Q_ijk=0 without a source/collision argument",
        "promote full_vlasov only after Janus phase-space transport is written",
        "use p0_janus_full_vlasov_moment_closure_contract before replacing EOS by f moments",
        "use p0_janus_pi_zero_preservation_gate before setting Pi_ij=0 outside dust",
        "use p0_janus_vlasov_geodesic_force_target to derive A^i_Janus from Gamma",
        "use p0_janus_eos_prho_no_go_vlasov_gate before requesting scalar p(rho)",
    ]
    return {
        "description": "Decision gate for admissible kinetic closure routes in Janus EOS/Pi work.",
        "status": "kinetic-closure-routes-decision-open",
        "depends_on": [
            "p0_janus_kinetic_moment_hierarchy_equations",
            "p0_janus_conditional_dust_branch_contract",
        ],
        "routes": routes,
        "next_work": next_work,
        "cold_dust_allowed_conditionally": True,
        "isotropic_dispersion_closed": False,
        "truncated_moment_allowed_without_source": False,
        "full_vlasov_route_selected": False,
        "full_vlasov_moment_closure_contract_available": True,
        "pi_zero_preservation_gate_available": True,
        "vlasov_geodesic_force_target_available": True,
        "eos_prho_no_go_vlasov_gate_available": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The only currently admissible closed branch is conditional cold dust. "
            "General EOS/Pi closure must use either a source-preserved isotropic distribution "
            "or a full Vlasov moment route; naive Q_ijk truncation is rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Kinetic Closure Routes Decision",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Cold dust allowed conditionally: {payload['cold_dust_allowed_conditionally']}",
        f"Isotropic dispersion closed: {payload['isotropic_dispersion_closed']}",
        f"Truncated moment allowed without source: {payload['truncated_moment_allowed_without_source']}",
        f"Full Vlasov route selected: {payload['full_vlasov_route_selected']}",
        "Full Vlasov moment closure contract available: "
        f"{payload['full_vlasov_moment_closure_contract_available']}",
        f"Pi zero preservation gate available: {payload['pi_zero_preservation_gate_available']}",
        f"Vlasov geodesic force target available: {payload['vlasov_geodesic_force_target_available']}",
        f"EOS p(rho) no-go Vlasov gate available: {payload['eos_prho_no_go_vlasov_gate_available']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Routes",
        "",
        "| route | closure rule | allowed | risk |",
        "|---|---|---|---|",
    ]
    for row in payload["routes"]:
        lines.append(f"| {row['route']} | `{row['closure_rule']}` | {row['allowed']} | {row['risk']} |")
    lines.extend(["", "## Next Work", ""])
    lines.extend(f"- {item}" for item in payload["next_work"])
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
