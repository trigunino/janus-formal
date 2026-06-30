from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_metric_tetrad_bridge.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_metric_tetrad_bridge.json")


def build_payload() -> dict:
    metric_branch = [
        {
            "sector": "plus",
            "metric": "ds_plus^2=-(1+2 Phi_plus)dt^2+(1-2 Psi_plus)delta_ij dx^i dx^j",
            "tetrad": "e_plus^0=(1+Phi_plus)dt, e_plus^i=(1-Psi_plus)dx^i",
        },
        {
            "sector": "minus",
            "metric": "ds_minus^2=-(1+2 Phi_minus)dt^2+(1-2 Psi_minus)delta_ij dx^i dx^j",
            "tetrad": "e_minus^0=(1+Phi_minus)dt, e_minus^i=(1-Psi_minus)dx^i",
        },
    ]
    source_equation_targets = [
        "Janus weak-field Poisson row for Phi_plus/Phi_minus from coupled field equations",
        "Janus weak-field spatial/slip row for Psi_plus/Psi_minus",
        "determinant convention fixing whether rho_minus is proper or positive-effective",
        "boundary/gauge condition fixing additive potential modes without observational fit",
        "mirror sign convention for plus-receives-minus and minus-receives-plus branches",
    ]
    bridge_chain = [
        {
            "step": "source_to_metric",
            "input": "Janus coupled weak-field source equations",
            "output": "Phi_plus, Phi_minus, Psi_plus, Psi_minus",
            "closed": False,
        },
        {
            "step": "metric_to_tetrad",
            "input": "weak-field metric potentials",
            "output": "linear tetrads e_plus/e_minus",
            "closed": True,
        },
        {
            "step": "tetrad_to_connection",
            "input": "e_plus/e_minus",
            "output": "relative spin-connection rows",
            "closed": True,
        },
        {
            "step": "connection_to_integrability",
            "input": "relative curvature rows",
            "output": "A_perp/R sparse PDE rows",
            "closed": False,
        },
    ]
    return {
        "description": "Bridge from Janus weak-field source equations to the restricted tetrad/curvature probes.",
        "status": "source-metric-tetrad-bridge-open",
        "metric_branch": metric_branch,
        "source_equation_targets": source_equation_targets,
        "bridge_chain": bridge_chain,
        "weakfield_metric_branch_written": True,
        "metric_to_tetrad_closed_at_linear_order": True,
        "tetrad_to_connection_closed_at_linear_order": True,
        "janus_source_potentials_derived": False,
        "determinant_density_convention_closed": False,
        "boundary_conditions_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The weak-field tetrad bridge is ready once Janus source equations provide "
            "Phi/Psi and the determinant-density convention. The bridge itself is not "
            "a fit and does not close the Janus perturbation problem."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Metric Tetrad Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weak-field metric branch written: {payload['weakfield_metric_branch_written']}",
        f"Metric to tetrad closed at linear order: {payload['metric_to_tetrad_closed_at_linear_order']}",
        f"Tetrad to connection closed at linear order: {payload['tetrad_to_connection_closed_at_linear_order']}",
        f"Janus source potentials derived: {payload['janus_source_potentials_derived']}",
        f"Determinant density convention closed: {payload['determinant_density_convention_closed']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Metric Branch",
        "",
        "| sector | metric | tetrad |",
        "|---|---|---|",
    ]
    for row in payload["metric_branch"]:
        lines.append(f"| {row['sector']} | `{row['metric']}` | `{row['tetrad']}` |")
    lines.extend(["", "## Source Equation Targets", ""])
    lines.extend(f"- {item}" for item in payload["source_equation_targets"])
    lines.extend(["", "## Bridge Chain", "", "| step | input | output | closed |", "|---|---|---|---|"])
    for row in payload["bridge_chain"]:
        lines.append(f"| {row['step']} | {row['input']} | {row['output']} | {row['closed']} |")
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
