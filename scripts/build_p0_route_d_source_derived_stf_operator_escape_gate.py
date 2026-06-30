from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_d_local_pde_no_selector_certificate import (
    build_payload as build_pde_certificate,
)
from scripts.build_p0_tracefree_h_source_action_provenance_chain_gate import (
    build_payload as build_tf_provenance,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_source_derived_stf_operator_escape_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_d_source_derived_stf_operator_escape_gate.json")


def build_payload() -> dict:
    certificate = build_pde_certificate()
    provenance = build_tf_provenance()
    required_chain = [
        "accepted Janus action/source with STF channel",
        "declared variation domain and boundary terms",
        "deltaS/deltaH or deltaS/deltaQ_TF derived",
        "P_STF projection after variation",
        "same bridge source term identified",
        "same-L Noether split closed",
        "principal symbol/stability screen passed",
    ]
    return {
        "description": (
            "Priority 3 gate for the only remaining Route D escape: a source-derived "
            "covariant STF curvature/operator that is not a free residual PDE."
        ),
        "status": "source-derived-stf-operator-escape-open",
        "pde_certificate_status": certificate["status"],
        "tracefree_provenance_status": provenance["status"],
        "required_chain": required_chain,
        "source_free_pde_excluded": bool(certificate["bounded_claim_closed"]),
        "only_open_escape": "source-derived STF curvature operator",
        "accepted_janus_action_exists": False,
        "accepted_operator_exists": False,
        "stf_source_action_provenance_closed": bool(provenance["source_action_provenance_closed"]),
        "same_bridge_source_term_closed": bool(provenance["same_bridge_source_term_closed"]),
        "residual_operator_allowed": False,
        "determinant_trace_allowed": False,
        "full_no_go_proved": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Route D is reduced to a single escape hatch: an accepted Janus-derived "
            "STF operator. It is not supplied yet; free residual operators, trace "
            "determinants, and source-free PDEs remain rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Source-Derived STF Operator Escape Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-free PDE excluded: {payload['source_free_pde_excluded']}",
        f"Only open escape: {payload['only_open_escape']}",
        f"Accepted Janus action exists: {payload['accepted_janus_action_exists']}",
        f"Accepted operator exists: {payload['accepted_operator_exists']}",
        f"STF source-action provenance closed: {payload['stf_source_action_provenance_closed']}",
        f"Same bridge source term closed: {payload['same_bridge_source_term_closed']}",
        f"Residual operator allowed: {payload['residual_operator_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Chain",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["required_chain"])
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
