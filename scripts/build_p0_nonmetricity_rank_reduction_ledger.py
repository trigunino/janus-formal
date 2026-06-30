from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_nonmetricity_integrability_curl_gate import (
    build_payload as build_integrability,
)
from scripts.build_p0_nonmetricity_mirror_inverse_gate import (
    build_payload as build_mirror,
)
from scripts.build_p0_nonmetricity_source_acceptance_criteria import (
    build_payload as build_acceptance,
)
from scripts.build_p0_sigma_trace_only_no_go_gate import (
    build_payload as build_trace_no_go,
)
from scripts.build_p0_tracefree_h_isotropy_no_go_gate import (
    build_payload as build_isotropy_no_go,
)
from scripts.build_p0_tracefree_h_projector_gate import (
    build_payload as build_tracefree_projector,
)
from scripts.build_p0_tracefree_h_source_candidate_matrix import (
    build_payload as build_source_candidates,
)


REPORT_PATH = Path("outputs/reports/p0_nonmetricity_rank_reduction_ledger.md")
JSON_PATH = Path("outputs/reports/p0_nonmetricity_rank_reduction_ledger.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank = dimension * (dimension + 1) // 2
    one_form_components = dimension * symmetric_rank
    trace_rank = dimension
    trace_free_one_form_components = one_form_components - trace_rank
    h_potential_components = symmetric_rank
    h_trace_free_components = symmetric_rank - 1
    trace_no_go = build_trace_no_go()
    tracefree_projector = build_tracefree_projector()
    source_candidates = build_source_candidates()
    isotropy_no_go = build_isotropy_no_go()
    integrability = build_integrability()
    mirror = build_mirror()
    acceptance = build_acceptance()
    rows = [
        {
            "gate": "definition",
            "effect": "N_alpha is D_alpha H, not an independent tensor one-form",
            "closed": True,
        },
        {
            "gate": "trace_only_no_go",
            "effect": "determinant/B4vol trace cannot select trace-free channel",
            "closed": bool(trace_no_go["no_go_closed"]),
        },
        {
            "gate": "tracefree_projector",
            "effect": "projector isolates the 9-component H_TF/Q_TF target",
            "closed": bool(tracefree_projector["projector_defined"]),
        },
        {
            "gate": "tracefree_source_candidates",
            "effect": "candidate tensor/action source routes are listed but not accepted",
            "closed": bool(not source_candidates["any_candidate_accepted"]),
        },
        {
            "gate": "isotropy_no_go",
            "effect": "density, pressure, determinant and FLRW scalar data cannot select Q_TF",
            "closed": bool(isotropy_no_go["isotropic_sources_have_zero_tf_projection"]),
        },
        {
            "gate": "curl_integrability",
            "effect": "N_alpha must integrate to one same H; arbitrary curls rejected",
            "closed": bool(integrability["source_n_integrability_proved"]),
        },
        {
            "gate": "mirror_inverse",
            "effect": "mirror N is induced by H^{-1}, not independent",
            "closed": bool(mirror["mirror_identity_closed"]),
        },
        {
            "gate": "source_acceptance",
            "effect": "source/action must select the remaining trace-free H or N branch",
            "closed": bool(acceptance["accepted_as_prediction_input"]),
        },
    ]
    return {
        "description": "Rank ledger for what remains open in the N_alpha/Phi_Sigma strain channel.",
        "status": "nonmetricity-rank-reduction-ledger-open",
        "dimension": dimension,
        "rank_counts": {
            "symmetric_H_components": symmetric_rank,
            "N_alpha_one_form_components_before_integrability": one_form_components,
            "trace_N_one_form_components": trace_rank,
            "trace_free_N_one_form_components_before_integrability": trace_free_one_form_components,
            "H_potential_components_after_integrability": h_potential_components,
            "trace_free_H_components_after_trace_split": h_trace_free_components,
        },
        "rows": rows,
        "algebraic_mirror_closed": bool(mirror["mirror_identity_closed"]),
        "trace_channel_insufficient": True,
        "source_trace_free_h_selected": False,
        "accepted_as_prediction_input": False,
        "prediction_ready": False,
        "verdict": (
            "After definition and integrability, the source problem is not an arbitrary "
            "40-component N one-form. It reduces to selecting a 4D symmetric H branch, "
            "or 9 trace-free H components after the determinant trace is separated. "
            "That trace-free source selection is still open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonmetricity Rank Reduction Ledger",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Algebraic mirror closed: {payload['algebraic_mirror_closed']}",
        f"Trace channel insufficient: {payload['trace_channel_insufficient']}",
        f"Source trace-free H selected: {payload['source_trace_free_h_selected']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Counts",
        "",
    ]
    for key, value in payload["rank_counts"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Gates", "", "| gate | effect | closed |", "|---|---|---:|"])
    for row in payload["rows"]:
        lines.append(f"| {row['gate']} | {row['effect']} | {row['closed']} |")
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
