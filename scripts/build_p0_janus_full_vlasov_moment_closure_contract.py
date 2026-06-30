from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_full_vlasov_moment_closure_contract.md")
JSON_PATH = Path("outputs/reports/p0_janus_full_vlasov_moment_closure_contract.json")


def build_payload() -> dict:
    moment_definitions = [
        {"moment": "density", "definition": "rho=int f dP"},
        {"moment": "mean_velocity", "definition": "rho beta_i=int v_i f dP"},
        {"moment": "pressure_tensor", "definition": "P_ij=int c_i c_j f dP with c_i=v_i-beta_i"},
        {"moment": "heat_flux", "definition": "Q_ijk=int c_i c_j c_k f dP"},
        {"moment": "pressure_scalar", "definition": "p=Tr(P_ij)/3"},
        {"moment": "anisotropic_stress", "definition": "Pi_ij=P_ij-p delta_ij"},
    ]
    source_requirements = [
        "derive A^i_Janus from Janus geodesics/source equations, not from a fit",
        "use the same L_minus_to_plus for kinetic stress transport and Q_cross projection",
        "fix the phase-space measure dP and B_4vol density convention",
        "couple f_plus and f_minus to the same source-selected metric/potential branch",
        "supply Janus initial and boundary data without sigma8/S8 renormalization",
    ]
    exact_closure_claims = [
        "finite M0/M1/M2 moment hierarchy is not closed by itself",
        "full f evolution makes P_ij and Q_ijk computable moment functionals",
        "Q_ijk is computed from f, not set to zero",
        "p(rho) is not implied unless a source-derived distribution family proves it",
    ]
    return {
        "description": "P0 contract for replacing finite EOS/Pi closure by full Janus Vlasov moment evolution.",
        "status": "full-vlasov-moment-closure-contract-open",
        "depends_on": [
            "p0_janus_kinetic_moment_hierarchy_equations",
            "p0_janus_kinetic_closure_routes_decision",
        "p0_stueckelberg_kinetic_transport_candidate",
            "p0_janus_vlasov_geodesic_force_target",
            "p0_janus_eos_prho_no_go_vlasov_gate",
        ],
        "phase_space_equation": (
            "D_t f + v^i D_i f + A^i_Janus[f_plus,f_minus,L,B_4vol] D_{v^i} f = 0"
        ),
        "moment_definitions": moment_definitions,
        "source_requirements": source_requirements,
        "exact_closure_claims": exact_closure_claims,
        "phase_space_equation_written": True,
        "moment_functionals_defined": True,
        "qijk_computed_not_truncated": True,
        "finite_moment_closure_claimed": False,
        "eos_prho_source_derived": False,
        "full_vlasov_contract_available": True,
        "vlasov_geodesic_force_target_available": True,
        "eos_prho_no_go_vlasov_gate_available": True,
        "janus_phase_space_transport_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The no-fit general route is full Vlasov evolution: solve f, then compute p, Pi, "
            "and Q_ijk as moments. This avoids a fake EOS but still needs source-derived "
            "Janus phase-space transport before any physics closure claim."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Full Vlasov Moment Closure Contract",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Phase-space equation: `{payload['phase_space_equation']}`",
        f"Phase-space equation written: {payload['phase_space_equation_written']}",
        f"Moment functionals defined: {payload['moment_functionals_defined']}",
        f"Q_ijk computed not truncated: {payload['qijk_computed_not_truncated']}",
        f"Finite moment closure claimed: {payload['finite_moment_closure_claimed']}",
        f"EOS p(rho) source-derived: {payload['eos_prho_source_derived']}",
        "Vlasov geodesic force target available: "
        f"{payload['vlasov_geodesic_force_target_available']}",
        "EOS p(rho) no-go Vlasov gate available: "
        f"{payload['eos_prho_no_go_vlasov_gate_available']}",
        f"Janus phase-space transport source-derived: {payload['janus_phase_space_transport_source_derived']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Moment Definitions",
        "",
    ]
    lines.extend(f"- {row['moment']}: `{row['definition']}`" for row in payload["moment_definitions"])
    lines.extend(["", "## Source Requirements", ""])
    lines.extend(f"- {item}" for item in payload["source_requirements"])
    lines.extend(["", "## Exact Closure Claims", ""])
    lines.extend(f"- {item}" for item in payload["exact_closure_claims"])
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
