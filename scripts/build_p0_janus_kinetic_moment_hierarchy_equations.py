from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_kinetic_moment_hierarchy_equations.md")
JSON_PATH = Path("outputs/reports/p0_janus_kinetic_moment_hierarchy_equations.json")


def build_payload() -> dict:
    moment_equations = [
        {
            "moment": "M0_continuity",
            "equation": "D_t rho + D_i(rho beta^i)=0",
            "new_unknown": "none beyond rho,beta",
            "closed_if": "beta is source-derived",
        },
        {
            "moment": "M1_momentum",
            "equation": "D_t(rho beta_i)+D_j(rho beta_i beta_j+P_ij)=rho F_i",
            "new_unknown": "P_ij",
            "closed_if": "second moment/effective pressure tensor is supplied",
        },
        {
            "moment": "M2_stress",
            "equation": "D_t P_ij + beta^k D_k P_ij + P_ik D_k beta_j + P_jk D_k beta_i + D_k Q_ijk = S_ij[F]",
            "new_unknown": "Q_ijk",
            "closed_if": "third moment/heat-flux closure or full f evolution is supplied",
        },
    ]
    decompositions = [
        "P_ij=p delta_ij+Pi_ij",
        "p=Tr(P_ij)/3",
        "Pi_ij=P_ij-p delta_ij",
        "Tr(Pi)=0",
    ]
    janus_source_links = [
        "G0i shift operator gives a momentum source target for beta_i in the dust/transverse limit",
        "M15/M30 source slots fix signs and determinant weights, not a closure for P_ij or Q_ijk",
        "X2025 kinetic source motivates Vlasov/Poisson route but does not close tensor Bianchi moments here",
    ]
    return {
        "description": "P0 kinetic moment hierarchy equations for deriving EOS and Pi without a fitted closure.",
        "status": "kinetic-moment-hierarchy-equations-open",
        "depends_on": [
            "p0_janus_kinetic_moment_eos_pi_closure_target",
            "p0_janus_weakfield_g0i_shift_operator_derivation",
            "p0_janus_eos_pi_source_audit",
        ],
        "moment_equations": moment_equations,
        "decompositions": decompositions,
        "janus_source_links": janus_source_links,
        "continuity_moment_written": True,
        "momentum_moment_written": True,
        "stress_moment_written": True,
        "pressure_pi_decomposition_available": True,
        "third_moment_required_for_general_closure": True,
        "vlasov_full_distribution_route_required": True,
        "hierarchy_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The moment hierarchy exposes the real blocker: pressure/Pi require the second moment, "
            "and second-moment evolution requires Q_ijk or the full Vlasov distribution. "
            "Dust is the cold conditional limit, not a general closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Kinetic Moment Hierarchy Equations",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Continuity moment written: {payload['continuity_moment_written']}",
        f"Momentum moment written: {payload['momentum_moment_written']}",
        f"Stress moment written: {payload['stress_moment_written']}",
        f"Pressure/Pi decomposition available: {payload['pressure_pi_decomposition_available']}",
        f"Third moment required for general closure: {payload['third_moment_required_for_general_closure']}",
        f"Vlasov full distribution route required: {payload['vlasov_full_distribution_route_required']}",
        f"Hierarchy closed: {payload['hierarchy_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Moment Equations",
        "",
        "| moment | equation | new unknown | closed if |",
        "|---|---|---|---|",
    ]
    for row in payload["moment_equations"]:
        lines.append(
            f"| {row['moment']} | `{row['equation']}` | `{row['new_unknown']}` | {row['closed_if']} |"
        )
    lines.extend(["", "## Decompositions", ""])
    lines.extend(f"- `{item}`" for item in payload["decompositions"])
    lines.extend(["", "## Janus Source Links", ""])
    lines.extend(f"- {item}" for item in payload["janus_source_links"])
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
