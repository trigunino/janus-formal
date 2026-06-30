from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_dl_source_law_traceability_gate import build_payload as build_dl_trace
from scripts.build_p0_falpha_free_components_gate import build_payload as build_free_components
from scripts.build_p0_falpha_minimal_gauge_candidate import build_payload as build_minimal_gauge
from scripts.build_p0_falpha_flow_projected_dl_residual_substitution import (
    build_payload as build_flow_substitution,
)
from scripts.build_p0_falpha_from_jacobian_tetrad_identity_target import (
    build_payload as build_jacobian_identity,
)


REPORT_PATH = Path("outputs/reports/p0_falpha_source_law_obligation_ledger.md")
JSON_PATH = Path("outputs/reports/p0_falpha_source_law_obligation_ledger.json")


def build_payload() -> dict:
    trace = build_dl_trace()
    free = build_free_components()
    minimal = build_minimal_gauge()
    flow = build_flow_substitution()
    jacobian_identity = build_jacobian_identity()
    obligation_rows = [
        {
            "id": "F-SRC",
            "obligation": "source_generator",
            "required_identity": "F_alpha from Janus map/source/connection equations",
            "current_anchor": "p0_dl_source_law_traceability_gate",
            "closed": trace["source_derived_dl_law_found"],
        },
        {
            "id": "F-LOR",
            "obligation": "lorentz_generator",
            "required_identity": "F_alpha^T eta + eta F_alpha = 0 from source-derived L",
            "current_anchor": "p0_dl_lorentz_generator_obstruction",
            "closed": False,
        },
        {
            "id": "F-FLOW",
            "obligation": "flow_projection",
            "required_identity": "flow-projected F rows cancel D_L velocity/tetrad residuals",
            "current_anchor": "p0_falpha_flow_projected_dl_residual_substitution",
            "closed": flow["falpha_source_derived"],
        },
        {
            "id": "F-JAC",
            "obligation": "jacobian_tetrad_identity",
            "required_identity": "D L from D J and tetrad derivatives with integrable source-selected J=dphi",
            "current_anchor": "p0_falpha_from_jacobian_tetrad_identity_target",
            "closed": jacobian_identity["falpha_source_derived"],
        },
        {
            "id": "F-FREE",
            "obligation": "transverse_free_components",
            "required_identity": "transverse/off-flow F components fixed by source or declared gauge principle",
            "current_anchor": "p0_falpha_free_components_gate",
            "closed": free["all_falpha_components_source_fixed"],
        },
        {
            "id": "F-MIN",
            "obligation": "minimal_gauge_not_source_law",
            "required_identity": "minimal gauge either derived from Janus or kept diagnostic",
            "current_anchor": "p0_falpha_minimal_gauge_candidate",
            "closed": minimal["source_derived_falpha"],
        },
        {
            "id": "F-MIR",
            "obligation": "mirror_inverse",
            "required_identity": "F_plus/F_minus follow from one inverse L, not independent choices",
            "current_anchor": "p0_source_derived_same_l_dl_residual_closure_target",
            "closed": False,
        },
    ]
    forbidden_operations = [
        "do not promote minimal-gauge F_alpha as source-derived",
        "do not set transverse F_alpha components to zero unless source/gauge derives it",
        "do not use separate F_alpha branches for K, Q_cross, and residuals",
        "do not fit F_alpha from lensing or residual cancellation",
    ]
    return {
        "description": "Obligation ledger for promoting F_alpha from constrained candidate to source law.",
        "status": "falpha-source-law-obligation-ledger-open",
        "depends_on": [
            "p0_dl_source_law_traceability_gate",
            "p0_falpha_free_components_gate",
            "p0_falpha_minimal_gauge_candidate",
            "p0_falpha_flow_projected_dl_residual_substitution",
            "p0_falpha_from_jacobian_tetrad_identity_target",
        ],
        "obligation_rows": obligation_rows,
        "forbidden_operations": forbidden_operations,
        "obligations_written": True,
        "source_law_derivation_found": False,
        "flow_rows_conditionally_reduced": flow["dl_rows_reduced_conditionally"],
        "jacobian_tetrad_identity_written": jacobian_identity["dl_identity_written"],
        "jacobian_tetrad_identity_numeric_closes": jacobian_identity["dl_identity_numeric_closes"],
        "source_selected_jacobian_found": jacobian_identity["source_selected_jacobian_found"],
        "minimal_gauge_declared": minimal["minimal_gauge_declared"],
        "minimal_gauge_promoted": False,
        "all_falpha_components_source_fixed": free["all_falpha_components_source_fixed"],
        "falpha_source_derived": False,
        "all_falpha_obligations_source_closed": all(row["closed"] for row in obligation_rows),
        "source_law_obligations_closed": False,
        "uses_observational_fit": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "F_alpha has constrained diagnostic branches, but no source law. "
            "Closure requires source-derived flow, transverse, Lorentz, and mirror rows."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Falpha Source-Law Obligation Ledger",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Flow rows conditionally reduced: {payload['flow_rows_conditionally_reduced']}",
        f"Jacobian/tetrad identity written: {payload['jacobian_tetrad_identity_written']}",
        f"Jacobian/tetrad identity numeric closes: {payload['jacobian_tetrad_identity_numeric_closes']}",
        f"Source-selected Jacobian found: {payload['source_selected_jacobian_found']}",
        f"Minimal gauge declared: {payload['minimal_gauge_declared']}",
        f"All Falpha obligations source-closed: {payload['all_falpha_obligations_source_closed']}",
        f"Source-law obligations closed: {payload['source_law_obligations_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Obligations",
        "",
        "| id | obligation | anchor | closed | required identity |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["obligation_rows"]:
        lines.append(
            f"| {row['id']} | {row['obligation']} | {row['current_anchor']} | "
            f"{row['closed']} | {row['required_identity']} |"
        )
    lines.extend(["", "## Forbidden Operations", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_operations"])
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
