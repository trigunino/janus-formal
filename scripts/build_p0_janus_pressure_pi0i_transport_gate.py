from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_pressure_pi0i_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_pressure_pi0i_transport_gate.json")


def build_payload() -> dict:
    tensor_terms = [
        {
            "term": "enthalpy_momentum",
            "formula": "(rho+p) gamma^2 beta_i",
            "must_transport": "rho, p, gamma, beta_i with same L and density convention",
            "closed": False,
        },
        {
            "term": "pressure_eos",
            "formula": "p=w rho or source-derived equation of state",
            "must_transport": "w/cross-pressure branch; cannot infer from dust",
            "closed": False,
        },
        {
            "term": "anisotropic_momentum",
            "formula": "Pi0i",
            "must_transport": "orientation/eigenframe and orthogonality u_A Pi^{AB}=0",
            "closed": False,
        },
        {
            "term": "projector",
            "formula": "h^{AB}=eta^{AB}+u^A u^B",
            "must_transport": "same transported u and L used for K and Q_cross",
            "closed": False,
        },
    ]
    forbidden = [
        "drop pressure in non-dust branches without source/equation-of-state proof",
        "set Pi0i=0 outside an eigenframe/isotropy proof",
        "absorb pressure or Pi0i momentum residuals into Q_det or Q_cross",
        "use a different L for Pi transport than for K and Q_cross",
    ]
    closure_chain = [
        "derive beta_i from Janus 0i source dynamics",
        "derive or choose equation-of-state branch from accepted Janus matter model",
        "transport Pi^{AB} with same Lorentz L or prove Pi^{AB}=0 in both sectors",
        "substitute T0i into plus/minus G0i source rows",
        "check R_plus=0 and R_minus=0 momentum components",
    ]
    return {
        "description": "P0 gate for transporting pressure and Pi0i momentum terms in Janus non-comoving sources.",
        "status": "pressure-pi0i-transport-open",
        "depends_on": [
            "p0_janus_weakfield_g0i_shift_operator_derivation",
            "p0_noncomoving_momentum_t0i_closure_target",
            "p0_bianchi_tensor_matter_extension_target",
        ],
        "tensor_terms": tensor_terms,
        "forbidden": forbidden,
        "closure_chain": closure_chain,
        "dust_limit_available": True,
        "perfect_fluid_pressure_transport_closed_algebraically": True,
        "anisotropic_pi0i_transport_closed_algebraically": True,
        "equation_of_state_source_derived": False,
        "pi_evolution_source_derived": False,
        "g0i_dust_beta_inversion_available": True,
        "matter_eos_pi_branch_decision_available": True,
        "same_l_for_pressure_pi_k_qcross_required": True,
        "qdet_qcross_absorption_forbidden": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The same-L tensor transport algebra is available in "
            "p0_janus_pressure_pi0i_transport_derivation. General non-comoving closure "
            "still requires source-derived equation of state, Pi evolution or Pi=0 proof, "
            "beta_i, and R_plus/R_minus cancellation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Pressure/Pi0i Transport Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust limit available: {payload['dust_limit_available']}",
        "Perfect-fluid pressure transport closed algebraically: "
        f"{payload['perfect_fluid_pressure_transport_closed_algebraically']}",
        "Anisotropic Pi0i transport closed algebraically: "
        f"{payload['anisotropic_pi0i_transport_closed_algebraically']}",
        f"Equation of state source-derived: {payload['equation_of_state_source_derived']}",
        f"Pi evolution source-derived: {payload['pi_evolution_source_derived']}",
        f"G0i dust beta inversion available: {payload['g0i_dust_beta_inversion_available']}",
        f"Matter EOS/Pi branch decision available: {payload['matter_eos_pi_branch_decision_available']}",
        f"Same L for pressure/Pi/K/Q_cross required: {payload['same_l_for_pressure_pi_k_qcross_required']}",
        f"Q_det/Q_cross absorption forbidden: {payload['qdet_qcross_absorption_forbidden']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Tensor Terms",
        "",
        "| term | formula | must transport | closed |",
        "|---|---|---|---|",
    ]
    for row in payload["tensor_terms"]:
        lines.append(f"| {row['term']} | `{row['formula']}` | {row['must_transport']} | {row['closed']} |")
    lines.extend(["", "## Forbidden", ""])
    lines.extend(f"- {item}" for item in payload["forbidden"])
    lines.extend(["", "## Closure Chain", ""])
    lines.extend(f"- {item}" for item in payload["closure_chain"])
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
