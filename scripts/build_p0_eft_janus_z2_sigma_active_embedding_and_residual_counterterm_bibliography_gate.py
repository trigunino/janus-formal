from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_active_embedding_and_residual_counterterm_bibliography_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_active_embedding_and_residual_counterterm_bibliography_gate.json"
)


def build_payload() -> dict:
    sources = [
        {
            "key": "Mars-Senovilla-2002",
            "url": "https://arxiv.org/abs/gr-qc/0201054",
            "supports": ["general hypersurface junctions", "distributional Bianchi identities"],
            "route": "active_embedding_second_form",
        },
        {
            "key": "Capovilla-Guven-1995",
            "url": "https://arxiv.org/abs/gr-qc/9411060",
            "supports": ["membrane deformations", "local geometric worldsheet scalars"],
            "route": "residual_counterterm_variation_audit",
        },
        {
            "key": "Carter-2000",
            "url": "https://arxiv.org/abs/gr-qc/0012036",
            "supports": ["brane force balance", "normal dynamics"],
            "route": "active_embedding_second_form",
        },
        {
            "key": "Dirac-relaxation-2006",
            "url": "https://arxiv.org/abs/gr-qc/0606098",
            "supports": ["active brane variation", "junction-condition relaxation"],
            "route": "active_embedding_second_form",
        },
        {
            "key": "Garcia-Lobo-Visser-2011",
            "url": "https://arxiv.org/abs/1112.2057",
            "supports": ["generic dynamic thin-shell route", "DeltaK from shell radius"],
            "route": "dynamic_shell_DeltaK_diagnostic",
        },
        {
            "key": "Lobo-Crawford-2005",
            "url": "https://arxiv.org/abs/gr-qc/0507063",
            "supports": ["momentum flux term", "radial shell balance"],
            "route": "dynamic_shell_DeltaK_diagnostic",
        },
        {
            "key": "Holst-1995",
            "url": "https://bpb-us-e2.wpmucdn.com/websites.umass.edu/dist/e/23826/files/2014/11/Holst.pdf",
            "supports": ["first-order Holst action", "tetrad/connection variation"],
            "route": "first_order_boundary_variation_counterterm_audit",
        },
        {
            "key": "Corichi-WilsonEwing-2010",
            "url": "https://arxiv.org/abs/1005.3298",
            "supports": ["Holst surface terms", "covariant symplectic current"],
            "route": "first_order_boundary_variation_counterterm_audit",
        },
        {
            "key": "Corichi-RubalcavaGarcia-Vukasinac-2016",
            "url": "https://arxiv.org/abs/1604.07764",
            "supports": ["first-order topological terms", "boundary conditions", "well-posed action"],
            "route": "first_order_boundary_variation_counterterm_audit",
        },
        {
            "key": "Oliveri-Speziale-2019",
            "url": "https://arxiv.org/abs/1912.01016",
            "supports": ["tetrad boundary variation", "exact-form mismatch vs metric boundary term"],
            "route": "tetrad_to_metric_boundary_variation_audit",
        },
        {
            "key": "Corichi-Reyes-2015",
            "url": "https://arxiv.org/abs/1505.01518",
            "supports": ["3+1 Holst Hamiltonian", "surface terms", "Poincare charges"],
            "route": "hamiltonian_boundary_charge_cross_check",
        },
    ]
    route_decision = {
        "DeltaK_route": "active_embedding_second_form_first",
        "f_pm_shortcut_allowed": False,
        "dynamic_thin_shell_route_status": "diagnostic_until_active_chart_or_embedding_supplied",
        "non_GHY_Rh_RK_status": "not_closed_by_bibliography",
        "Holst_boundary_variation_status": (
            "supports theta(e,omega) and surface-term bookkeeping; torsionless "
            "Holst does not determine non-GHY R_h/R_K traces"
        ),
        "tetrad_metric_mapping_status": (
            "tetrad boundary variation differs from metric by exact form; useful "
            "audit, not a unique Sigma density"
        ),
        "counterterm_policy": "audit_or_eliminate_residuals; do_not_add_artificial_S_ct",
    }
    blockers = [
        "R_Sigma_solution_certificate",
        "active_embedding_manifest",
        "metric_non_GHY_trace_R_h",
        "extrinsic_non_GHY_trace_R_K",
    ]
    return {
        "status": "janus-z2-sigma-active-embedding-and-residual-counterterm-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "sources": sources,
        "route_decision": route_decision,
        "active_embedding_route_selected": True,
        "non_GHY_counterterm_closes_for_free": False,
        "artificial_counterterm_forbidden": True,
        "primary_blockers": blockers,
        "gate_passed": True,
        "next_required": [
            "audit_or_eliminate_metric_non_GHY_trace_R_h",
            "audit_or_eliminate_extrinsic_non_GHY_trace_R_K",
            "derive_R_Sigma_solution_certificate_from_allowed_radial_blocks",
            "materialize_active_embedding_manifest",
            "compute_DeltaK_from_embedding_second_form",
            "project_Holst_Palatini_boundary_theta_to_Sigma_PT67_variables",
            "extract_or_eliminate_R_h_trace_and_R_K_trace_from_that_projection",
        ],
        "verdict": (
            "Bibliography supports the active embedding/second-form route for DeltaK "
            "and supports auditing local geometric counterterm variations. It does "
            "not justify a free non-GHY S_ct, an f_pm shortcut, or a counterterm "
            "component without explicit R_h/R_K traces."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Active Embedding and Residual Counterterm Bibliography Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Active embedding route selected: `{payload['active_embedding_route_selected']}`",
        f"Non-GHY closes for free: `{payload['non_GHY_counterterm_closes_for_free']}`",
        "",
        payload["verdict"],
        "",
        "## Route decision",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["route_decision"].items())
    lines.extend(["", "## Sources"])
    lines.extend(f"- `{item['key']}`: {item['url']}" for item in payload["sources"])
    lines.extend(["", "## Next required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
