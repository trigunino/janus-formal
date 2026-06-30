from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_minimal_nonrustine_extension_contract import (
    build_payload as build_contract,
)
from scripts.build_p0_route_c_pt_geometry_path_rule_audit import (
    build_payload as build_pt_audit,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_pt_fixed_path_extension_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_pt_fixed_path_extension_candidate_gate.json")


def build_payload() -> dict:
    contract = build_contract()
    pt_audit = build_pt_audit()
    rows = [
        {
            "requirement": "pt_invariant_path_functional",
            "meaning": "a scalar action/cost for cross-sector paths whose extrema define the path family",
            "closed": False,
        },
        {
            "requirement": "source_derived_boundary_or_throat",
            "meaning": "PT-fixed surface or transition condition must follow from Janus equations",
            "closed": False,
        },
        {
            "requirement": "same_l_transport_stack",
            "meaning": "the selected path must feed K, Q_cross, Vlasov moments and mirror inverse",
            "closed": False,
        },
        {
            "requirement": "two_path_noncommuting_resolution",
            "meaning": "the rule must choose between x-then-y and y-then-x without observational fit",
            "closed": False,
        },
        {
            "requirement": "stability_and_caustic_screen",
            "meaning": "path extrema must avoid ghost/caustic/multivalued hidden branches",
            "closed": False,
        },
        {
            "requirement": "source_traceability",
            "meaning": "if not published Janus, it must be declared as a new extension axiom",
            "closed": False,
        },
    ]
    return {
        "description": (
            "Gate for the only clean PT-based Route C extension candidate: a "
            "PT-fixed path functional or boundary law. This is not adopted."
        ),
        "status": "pt-fixed-path-extension-candidate-not-adopted",
        "depends_on": [
            "p0_route_c_pt_geometry_path_rule_audit",
            "p0_minimal_nonrustine_extension_contract",
        ],
        "pt_audit_status": pt_audit["status"],
        "minimal_contract_status": contract["status"],
        "rows": rows,
        "pt_extension_candidate_written": True,
        "pt_extension_adopted": False,
        "zero_axiom_source_derived": False,
        "new_axiom_risk": True,
        "requires_same_l": True,
        "requires_mirror_inverse": True,
        "requires_no_fit": True,
        "forbids_qdet_qcross_absorption": True,
        "can_be_used_for_prediction_now": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A PT-fixed path functional is the sharpest non-rustine candidate if "
            "PT geometry is pursued. It remains an extension candidate only: no "
            "current Janus source derives the functional, boundary law, or same-L "
            "path selector."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C PT-Fixed Path Extension Candidate Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"PT extension candidate written: {payload['pt_extension_candidate_written']}",
        f"PT extension adopted: {payload['pt_extension_adopted']}",
        f"Zero-axiom source derived: {payload['zero_axiom_source_derived']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Requires same L: {payload['requires_same_l']}",
        f"Requires mirror inverse: {payload['requires_mirror_inverse']}",
        f"Requires no fit: {payload['requires_no_fit']}",
        f"Forbids Qdet/Qcross absorption: {payload['forbids_qdet_qcross_absorption']}",
        f"Can be used for prediction now: {payload['can_be_used_for_prediction_now']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| requirement | meaning | closed |",
        "|---|---|---:|",
    ]
    for row in payload["rows"]:
        lines.append(f"| {row['requirement']} | {row['meaning']} | {row['closed']} |")
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
