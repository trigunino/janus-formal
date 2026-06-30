from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_matter_eos_pi_branch_decision.md")
JSON_PATH = Path("outputs/reports/p0_janus_matter_eos_pi_branch_decision.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "dust",
            "assumption": "p=0 and Pi^{AB}=0",
            "source_status": "conditional matter model, not general Janus EOS",
            "what_closes": "pressure/Pi0i terms vanish; G0i dust beta inversion applies",
            "physics_closed": False,
        },
        {
            "branch": "perfect_fluid",
            "assumption": "p=w rho",
            "source_status": "requires source-derived w or accepted EOS branch",
            "what_closes": "only after w_cross and pressure gradients are derived",
            "physics_closed": False,
        },
        {
            "branch": "anisotropic_stress",
            "assumption": "Pi^{AB} nonzero",
            "source_status": "requires Pi evolution or eigenframe/isotropy proof",
            "what_closes": "orientation and Pi0i terms only after tensor evolution closes",
            "physics_closed": False,
        },
    ]
    source_facts = [
        "M15 records signs rho(+)>0,p(+)>0 and rho(-)<0,p(-)<0",
        "M15 source slots do not by themselves provide an equation of state p=w rho",
        "dust remains a conditional simplification, not a general matter theorem",
    ]
    return {
        "description": "Decision gate for Janus matter EOS and Pi branches after pressure/Pi0i algebra.",
        "status": "matter-eos-pi-branch-decision-open",
        "branches": branches,
        "source_facts": source_facts,
        "dust_branch_conditionally_available": True,
        "dust_branch_general_matter_proof": False,
        "perfect_fluid_eos_source_derived": False,
        "anisotropic_pi_evolution_source_derived": False,
        "pi_zero_source_proved": False,
        "g0i_dust_beta_inversion_available": True,
        "eos_pi_source_audit_available": True,
        "conditional_dust_branch_contract_available": True,
        "kinetic_moment_eos_pi_closure_target_available": True,
        "kinetic_moment_hierarchy_equations_available": True,
        "kinetic_closure_routes_decision_available": True,
        "full_vlasov_moment_closure_contract_available": True,
        "pi_zero_preservation_gate_available": True,
        "vlasov_geodesic_force_target_available": True,
        "eos_prho_no_go_vlasov_gate_available": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Use dust only as an explicit conditional branch. General Janus matter still needs "
            "a source-derived EOS and either Pi evolution or a source proof that Pi vanishes."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Matter EOS/Pi Branch Decision",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust branch conditionally available: {payload['dust_branch_conditionally_available']}",
        f"Dust branch general matter proof: {payload['dust_branch_general_matter_proof']}",
        f"Perfect-fluid EOS source-derived: {payload['perfect_fluid_eos_source_derived']}",
        f"Anisotropic Pi evolution source-derived: {payload['anisotropic_pi_evolution_source_derived']}",
        f"Pi zero source proved: {payload['pi_zero_source_proved']}",
        f"G0i dust beta inversion available: {payload['g0i_dust_beta_inversion_available']}",
        f"EOS/Pi source audit available: {payload['eos_pi_source_audit_available']}",
        f"Conditional dust branch contract available: {payload['conditional_dust_branch_contract_available']}",
        "Kinetic moment EOS/Pi closure target available: "
        f"{payload['kinetic_moment_eos_pi_closure_target_available']}",
        "Kinetic moment hierarchy equations available: "
        f"{payload['kinetic_moment_hierarchy_equations_available']}",
        "Kinetic closure routes decision available: "
        f"{payload['kinetic_closure_routes_decision_available']}",
        "Full Vlasov moment closure contract available: "
        f"{payload['full_vlasov_moment_closure_contract_available']}",
        f"Pi zero preservation gate available: {payload['pi_zero_preservation_gate_available']}",
        f"Vlasov geodesic force target available: {payload['vlasov_geodesic_force_target_available']}",
        f"EOS p(rho) no-go Vlasov gate available: {payload['eos_prho_no_go_vlasov_gate_available']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Facts",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["source_facts"])
    lines.extend(["", "## Branches", "", "| branch | assumption | source status | what closes | physics closed |", "|---|---|---|---|---|"])
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | `{row['assumption']}` | {row['source_status']} | "
            f"{row['what_closes']} | {row['physics_closed']} |"
        )
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
