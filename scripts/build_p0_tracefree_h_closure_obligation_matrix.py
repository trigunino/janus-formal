from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_action_operator_requirements_gate import (
    build_payload as build_action_operator,
)
from scripts.build_p0_tracefree_h_irrep_source_requirements_gate import (
    build_payload as build_irrep_source,
)
from scripts.build_p0_tracefree_h_scalar_vector_no_go_gate import (
    build_payload as build_scalar_vector_no_go,
)
from scripts.build_p0_tracefree_h_source_candidate_matrix import (
    build_payload as build_candidates,
)
from scripts.build_p0_tracefree_h_variational_source_template_gate import (
    build_payload as build_variational_template,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_closure_obligation_matrix.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_closure_obligation_matrix.json")


def build_payload() -> dict:
    irrep = build_irrep_source()
    operator = build_action_operator()
    candidates = build_candidates()
    scalar_vector_no_go = build_scalar_vector_no_go()
    variational_template = build_variational_template()
    target_equation = "P_STF(E_H[H,L,phi] - S_TF^Janus[matter,geometry,L,phi]) = 0"
    obligations = [
        {
            "obligation": "stf_source_type",
            "requires": "S_TF^Janus is a covariant symmetric trace-free rank-2 tensor in the same bridge",
            "closed": bool(irrep["source_selection_closed"]),
        },
        {
            "obligation": "stf_el_operator",
            "requires": "E_H is an Euler-Lagrange operator projected with P_STF",
            "closed": bool(operator["stf_el_operator_supplied"]),
        },
        {
            "obligation": "source_provenance",
            "requires": "all source terms derive from published Janus equations or an accepted Janus action",
            "closed": bool(variational_template["requirements_closed"]),
        },
        {
            "obligation": "scalar_vector_no_go",
            "requires": "rho, p, B4vol, Q_det, single vectors and gradients are rejected as selectors",
            "closed": bool(
                scalar_vector_no_go["scalar_stf_projection_zero"]
                and not scalar_vector_no_go["single_vector_gradient_covariant_stf_selector"]
                and not scalar_vector_no_go["derivative_ansatz_accepted"]
            ),
        },
        {
            "obligation": "candidate_selection",
            "requires": "one Q_TF candidate route is accepted without residual fitting",
            "closed": bool(candidates["any_candidate_accepted"]),
        },
        {
            "obligation": "curl_integrability",
            "requires": "D H / D Q integrates to one same H branch",
            "closed": False,
        },
        {
            "obligation": "mirror_inverse",
            "requires": "minus branch is induced by H^{-1}, not an independent tensor source",
            "closed": False,
        },
        {
            "obligation": "same_l_transport",
            "requires": "same L feeds K_plus, K_minus, Q_cross, optics and Vlasov moments",
            "closed": False,
        },
        {
            "obligation": "gauge_boundary",
            "requires": "boundary and gauge conditions are fixed before observations",
            "closed": False,
        },
        {
            "obligation": "ghost_stability",
            "requires": "principal symbol has no ghost/tachyon branch for propagating strain",
            "closed": False,
        },
    ]
    return {
        "description": "Closure obligations for turning trace-free H/Q_TF into a Janus prediction input.",
        "status": "tracefree-h-closure-obligations-open",
        "target_equation": target_equation,
        "depends_on": [
            "p0_tracefree_h_irrep_source_requirements_gate",
            "p0_tracefree_h_action_operator_requirements_gate",
            "p0_tracefree_h_source_candidate_matrix",
            "p0_tracefree_h_scalar_vector_no_go_gate",
            "p0_tracefree_h_variational_source_template_gate",
            "p0_nonmetricity_integrability_curl_gate",
            "p0_nonmetricity_mirror_inverse_gate",
            "p0_janus_same_l_transport_stack_gate",
        ],
        "obligations": obligations,
        "obligations_closed": sum(1 for row in obligations if row["closed"]),
        "obligations_total": len(obligations),
        "accepted_as_prediction_input": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "forbidden_shortcuts": [
            "replace S_TF^Janus by rho, p, B4vol, Q_det, or any scalar trace",
            "choose S_TF^Janus from residual cancellation",
            "reuse a 2D screen/shear observable as a 4D source law",
            "accept a derivative action without stability and boundary/gauge checks",
        ],
        "verdict": (
            "The next non-rustine target is not another candidate name. It is the "
            "source-derived STF equation P_STF(E_H - S_TF^Janus)=0, with provenance, "
            "integrability, mirror, same-L, gauge and stability obligations closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Closure Obligation Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target equation: `{payload['target_equation']}`",
        f"Obligations closed: {payload['obligations_closed']}/{payload['obligations_total']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Obligations",
        "",
        "| obligation | requires | closed |",
        "|---|---|---:|",
    ]
    for row in payload["obligations"]:
        lines.append(f"| {row['obligation']} | {row['requires']} | {row['closed']} |")
    lines.extend(["", "## Depends On", ""])
    lines.extend(f"- `{item}`" for item in payload["depends_on"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
