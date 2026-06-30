from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from scripts.build_p0_tracefree_h_variational_action_basis_gate import (
        build_payload as build_action_basis_payload,
    )
except ImportError:  # pragma: no cover - keeps this bounded artifact standalone.
    build_action_basis_payload = None


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_action_basis_acceptance_filter.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_action_basis_acceptance_filter.json")

ACCEPTANCE_COLUMNS = [
    {"key": "janus_provenance", "label": "Janus provenance"},
    {"key": "stf_el_operator", "label": "STF EL operator"},
    {"key": "boundary_gauge", "label": "boundary/gauge"},
    {"key": "same_l", "label": "same-L"},
    {"key": "mirror_inverse", "label": "mirror inverse"},
    {"key": "ghost_stability", "label": "ghost/stability"},
    {"key": "no_residual_no_determinant", "label": "no residual/no determinant"},
]

CLASS_ORDER = [
    "ultralocal invariants",
    "derivative kinetic",
    "linear couplings",
    "BF/GL constraints",
]

FALLBACK_TERMS = [
    {"term": "tr_qtf2", "class": "ultralocal invariant"},
    {"term": "tr_qtf3", "class": "ultralocal invariant"},
    {"term": "dqtf_kinetic", "class": "derivative kinetic"},
    {"term": "dhtf_kinetic", "class": "derivative kinetic"},
    {"term": "qtf_pi_tf", "class": "linear coupling"},
    {"term": "qtf_weyl", "class": "linear coupling"},
    {"term": "qtf_phi_sigma", "class": "linear coupling"},
    {"term": "bf_gl_constraints", "class": "constraint coupling"},
]


def _action_basis_payload() -> dict:
    if build_action_basis_payload is None:
        return {
            "status": "fallback-action-basis",
            "candidate_terms": FALLBACK_TERMS,
        }
    return build_action_basis_payload()


def _candidate_class(term: dict) -> str:
    if term["class"] == "ultralocal invariant":
        return "ultralocal invariants"
    if term["class"] == "linear coupling":
        return "linear couplings"
    if term["term"] == "bf_gl_constraints":
        return "BF/GL constraints"
    return term["class"]


def _rows_from_terms(terms: list[dict]) -> list[dict]:
    grouped = {name: [] for name in CLASS_ORDER}
    for term in terms:
        grouped[_candidate_class(term)].append(term["term"])

    blockers = {
        "ultralocal invariants": (
            "no Janus source/action provenance and no accepted STF EL operator"
        ),
        "derivative kinetic": (
            "derivative branch needs Janus source/action provenance first"
        ),
        "linear couplings": (
            "linear coupling branch needs Janus source/action provenance first"
        ),
        "BF/GL constraints": (
            "BF/GL constraint route needs Janus source/action provenance first"
        ),
    }
    rows = []
    for candidate_class in CLASS_ORDER:
        row = {
            "candidate_class": candidate_class,
            "terms": grouped[candidate_class],
            "janus_provenance": False,
            "stf_el_operator": False,
            "boundary_gauge": False,
            "same_l": False,
            "mirror_inverse": False,
            "ghost_stability": False,
            "no_residual_no_determinant": True,
            "blocker": blockers[candidate_class],
            "accepted": False,
            "prediction": False,
        }
        rows.append(row)
    return rows


def build_payload() -> dict:
    action_basis = _action_basis_payload()
    filter_rows = _rows_from_terms(action_basis["candidate_terms"])
    return {
        "description": (
            "Bounded P0 acceptance filter for trace-free H/Q_TF action-basis "
            "candidate classes."
        ),
        "status": "tracefree-h-action-basis-acceptance-filter-open",
        "source_artifact": "p0_tracefree_h_variational_action_basis_gate",
        "source_status": action_basis["status"],
        "acceptance_columns": ACCEPTANCE_COLUMNS,
        "candidate_classes": CLASS_ORDER,
        "candidate_class_count": len(filter_rows),
        "filter_rows": filter_rows,
        "all_fail_janus_provenance": all(
            not row["janus_provenance"] for row in filter_rows
        ),
        "accepted_classes": [
            row["candidate_class"] for row in filter_rows if row["accepted"]
        ],
        "any_class_accepted": False,
        "best_next_branch": {
            "classes": ["derivative kinetic", "linear couplings"],
            "allowed_now": False,
            "condition": "only after source/action provenance",
        },
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "No action-basis class is accepted. The best next branch is "
            "derivative/linear coupling only after source/action provenance."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Action-Basis Acceptance Filter",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source artifact: {payload['source_artifact']}",
        f"Source status: {payload['source_status']}",
        f"Candidate classes: {payload['candidate_class_count']}",
        f"All fail Janus provenance: {payload['all_fail_janus_provenance']}",
        f"Any class accepted: {payload['any_class_accepted']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Acceptance Filter",
        "",
        (
            "| candidate class | terms | Janus provenance | STF EL operator | "
            "boundary/gauge | same-L | mirror inverse | ghost/stability | "
            "no residual/no determinant | accepted | prediction | blocker |"
        ),
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row in payload["filter_rows"]:
        lines.append(
            f"| {row['candidate_class']} | `{', '.join(row['terms'])}` | "
            f"{row['janus_provenance']} | {row['stf_el_operator']} | "
            f"{row['boundary_gauge']} | {row['same_l']} | "
            f"{row['mirror_inverse']} | {row['ghost_stability']} | "
            f"{row['no_residual_no_determinant']} | {row['accepted']} | "
            f"{row['prediction']} | {row['blocker']} |"
        )
    branch = payload["best_next_branch"]
    lines.extend(
        [
            "",
            "## Best Next Branch",
            "",
            f"- classes: `{', '.join(branch['classes'])}`",
            f"- allowed now: `{branch['allowed_now']}`",
            f"- condition: {branch['condition']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
