from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_vlasov_quadrupole_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_vlasov_quadrupole_gate.json")


def build_payload() -> dict:
    moment_definitions = [
        {
            "moment": "density",
            "formula": "rho=m int f dmu_L",
            "role": "zeroth phase-space moment",
        },
        {
            "moment": "pressure",
            "formula": "p=Tr(P_ij)/3",
            "role": "isotropic second moment",
        },
        {
            "moment": "pi_tf_quadrupole",
            "formula": "Pi_TF_ij=P_ij-p delta_ij",
            "role": "trace-free second moment / quadrupole",
        },
    ]
    hierarchy_couplings = [
        {
            "equation": "density_continuity",
            "depends_on": "momentum / first moment",
            "closed": "conditional",
        },
        {
            "equation": "pressure_pi_transport",
            "depends_on": "third moment / heat flux",
            "closed": False,
        },
        {
            "equation": "quadrupole_evolution",
            "depends_on": "higher moments / Vlasov moment tower",
            "closed": False,
        },
    ]
    acceptance_requirements = [
        {
            "requirement": "Janus kinetic action/source",
            "closed": False,
            "reason": "Q_TF source must be selected by Janus dynamics, not named by hand",
        },
        {
            "requirement": "same-L phase-space measure",
            "closed": False,
            "reason": "moments must use the same L-sector measure as the trace-free H source",
        },
        {
            "requirement": "moment hierarchy or full Vlasov transport",
            "closed": False,
            "reason": "Pi_TF evolution couples to higher moments",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for Vlasov quadrupole/Pi_TF as a trace-free "
            "H/Q_TF source candidate."
        ),
        "status": "tracefree-h-vlasov-quadrupole-candidate-open",
        "qtf_candidate": "kinetic_quadrupole_vlasov",
        "moment_definitions": moment_definitions,
        "quadrupole_definition": {
            "stress": "P_ij=m int c_i c_j f dmu_L",
            "pressure": "p=Tr(P_ij)/3",
            "trace_free_quadrupole": "Pi_TF_ij=P_ij-p delta_ij",
            "trace_test": "delta^ij Pi_TF_ij=0",
        },
        "hierarchy_couplings": hierarchy_couplings,
        "acceptance_requirements": acceptance_requirements,
        "distribution_defines_density_pressure_pi_tf": True,
        "trace_free_quadrupole_defined": True,
        "moment_hierarchy_closed": False,
        "full_vlasov_transport_closed": False,
        "quadrupole_evolution_algebraically_closed": False,
        "janus_kinetic_action_source_closed": False,
        "same_l_phase_space_measure_closed": False,
        "uses_observational_fit": False,
        "uses_residual_fit": False,
        "can_source_qtf": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not treat Pi_TF definition as Pi_TF evolution closure",
            "do not close the quadrupole algebraically; it couples to higher moments",
            "do not use observational or residual fits as Q_TF source selection",
            "require Janus kinetic action/source and same-L phase-space measure first",
        ],
        "verdict": (
            "A distribution f can define density, pressure, and Pi_TF/quadrupole. "
            "It cannot source Q_TF until Janus kinetic dynamics and the same-L "
            "phase-space measure close the Vlasov hierarchy."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Vlasov Quadrupole Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Q_TF candidate: {payload['qtf_candidate']}",
        (
            "Distribution defines density/pressure/Pi_TF: "
            f"{payload['distribution_defines_density_pressure_pi_tf']}"
        ),
        f"Trace-free quadrupole defined: {payload['trace_free_quadrupole_defined']}",
        f"Moment hierarchy closed: {payload['moment_hierarchy_closed']}",
        f"Full Vlasov transport closed: {payload['full_vlasov_transport_closed']}",
        (
            "Quadrupole evolution algebraically closed: "
            f"{payload['quadrupole_evolution_algebraically_closed']}"
        ),
        f"Janus kinetic action/source closed: {payload['janus_kinetic_action_source_closed']}",
        f"Same-L phase-space measure closed: {payload['same_l_phase_space_measure_closed']}",
        f"Can source Q_TF: {payload['can_source_qtf']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses residual fit: {payload['uses_residual_fit']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Moment Definitions",
        "",
        "| moment | formula | role |",
        "|---|---|---|",
    ]
    for row in payload["moment_definitions"]:
        lines.append(f"| {row['moment']} | `{row['formula']}` | {row['role']} |")
    lines.extend(["", "## Quadrupole Definition", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["quadrupole_definition"].items())
    lines.extend(
        [
            "",
            "## Hierarchy Couplings",
            "",
            "| equation | depends on | closed |",
            "|---|---|---:|",
        ]
    )
    for row in payload["hierarchy_couplings"]:
        lines.append(f"| {row['equation']} | {row['depends_on']} | {row['closed']} |")
    lines.extend(
        [
            "",
            "## Acceptance Requirements",
            "",
            "| requirement | closed | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["acceptance_requirements"]:
        lines.append(f"| {row['requirement']} | {row['closed']} | {row['reason']} |")
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
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
