from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload as build_minimal_spath,
)
from scripts.build_p0_route_c_spath_scalar_density_completion_gate import (
    build_payload as build_scalar_density,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_metric_stress_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_metric_stress_variation_gate.json")


def build_payload() -> dict:
    minimal = build_minimal_spath()
    scalar_density = build_scalar_density()
    variation_rows = [
        {
            "object": "Hilbert_stress_definition",
            "formula": "K_s^{mu nu}=(-2/sqrt(-g_s)) delta S_path/delta g^s_{mu nu}",
            "written": True,
            "closed": False,
            "blocker": "S_path is not yet a full scalar density in g_plus and g_minus",
        },
        {
            "object": "volume_density",
            "formula": "delta sqrt(-g_s) = -1/2 sqrt(-g_s) g^s_{mu nu} delta g_s^{mu nu}",
            "written": True,
            "closed": True,
            "blocker": "none for the standard volume identity",
        },
        {
            "object": "path_cost_metric_chain",
            "formula": "delta C_J = (partial C_J/partial g_s) delta g_s + (partial C_J/partial Gamma_s) delta Gamma_s",
            "written": True,
            "closed": False,
            "blocker": "C_J/V_J are not source-fixed functions of Janus fields",
        },
        {
            "object": "lorentz_transport_metric_chain",
            "formula": "delta(D_s L)=delta omega_plus L - L delta omega_minus + metric/tetrad terms",
            "written": True,
            "closed": False,
            "blocker": "tetrad/spin-connection dependence of S_path is not fully specified",
        },
        {
            "object": "boundary_metric_chain",
            "formula": "delta B_PT/delta g_s plus endpoint variations",
            "written": True,
            "closed": False,
            "blocker": "PT boundary law is not selected",
        },
        {
            "object": "pressure_pi_tensor_extraction",
            "formula": "P_perp K_s -> pressure term and STF(P_perp K_s) -> Pi_s^{mu nu}",
            "written": True,
            "closed": False,
            "blocker": "pressure/Pi require tensor variation, not scalar Q absorption",
        },
    ]
    return {
        "description": (
            "Metric-stress variation gate for the explicit S_path extension. "
            "It records the exact tensor variation obligations needed to derive "
            "K_plus/K_minus rather than postulate them."
        ),
        "status": "spath-metric-stress-variation-gate-open",
        "depends_on": [
            "p0_route_c_minimal_spath_extension_axiom_gate",
            "p0_route_c_spath_scalar_density_completion_gate",
        ],
        "minimal_spath_status": minimal["status"],
        "scalar_density_contract_written": bool(scalar_density["scalar_density_contract_written"]),
        "scalar_density_complete": bool(scalar_density["scalar_density_complete"]),
        "variation_rows": variation_rows,
        "hilbert_stress_definition_written": True,
        "volume_variation_identity_closed": True,
        "metric_variation_chain_written": True,
        "metric_variation_chain_complete": False,
        "k_plus_metric_variation_derived": False,
        "k_minus_metric_variation_derived": False,
        "pressure_pi_tensor_terms_derived": False,
        "boundary_metric_variation_fixed": False,
        "scalar_absorption_allowed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The Hilbert-stress route is now explicit, but not closed: only the "
            "standard volume variation is complete. C_J/V_J, spin/tetrad chains, "
            "PT boundary data, and pressure/Pi tensor extraction remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Metric-Stress Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scalar density contract written: {payload['scalar_density_contract_written']}",
        f"Scalar density complete: {payload['scalar_density_complete']}",
        f"Hilbert stress definition written: {payload['hilbert_stress_definition_written']}",
        f"Volume variation identity closed: {payload['volume_variation_identity_closed']}",
        f"Metric variation chain written: {payload['metric_variation_chain_written']}",
        f"Metric variation chain complete: {payload['metric_variation_chain_complete']}",
        f"K_plus metric variation derived: {payload['k_plus_metric_variation_derived']}",
        f"K_minus metric variation derived: {payload['k_minus_metric_variation_derived']}",
        f"Pressure/Pi tensor terms derived: {payload['pressure_pi_tensor_terms_derived']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| object | formula | written | closed | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["variation_rows"]:
        lines.append(
            f"| {row['object']} | `{row['formula']}` | {row['written']} | "
            f"{row['closed']} | {row['blocker']} |"
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
