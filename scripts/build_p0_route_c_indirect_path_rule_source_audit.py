from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_janus_path_rule_source_derivation_gate import (
    build_payload as build_path_source,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_indirect_path_rule_source_audit.md")
JSON_PATH = Path("outputs/reports/p0_route_c_indirect_path_rule_source_audit.json")


def build_payload() -> dict:
    path_source = build_path_source()
    rows = [
        {
            "source": "bianchi_divergence",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "divergence identities constrain residuals but do not choose a holonomy path family",
        },
        {
            "source": "noether_identity",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "requires an accepted action/multiplier that is not supplied",
        },
        {
            "source": "coupled_geodesics",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "geodesics define curves inside sectors, not the cross-sector same-L path rule",
        },
        {
            "source": "mirror_symmetry",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "mirror inverse constrains accepted paths but does not select one",
        },
        {
            "source": "pt_geometry",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "PT involution/parity filters branches and endpoints but does not choose a cross-sector holonomy path",
        },
        {
            "source": "flrw_perturbed_limit",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "background normal rule does not promote to perturbed/noncommuting holonomy",
        },
        {
            "source": "kinetic_sheet_vlasov",
            "could_filter": True,
            "selects_path_rule": False,
            "blocker": "sheet transport needs creation/path rules before it can select L",
        },
    ]
    return {
        "description": (
            "Route C indirect-source audit for the holonomy path rule: Bianchi, "
            "Noether, geodesics, mirror symmetry, FLRW limits, and kinetic sheets "
            "are tested as possible zero-axiom sources."
        ),
        "status": "indirect-path-rule-source-audit-open",
        "path_source_status": path_source["status"],
        "rows": rows,
        "audited_source_count": len(rows),
        "accepted_indirect_source_count": sum(1 for row in rows if row["selects_path_rule"]),
        "indirect_path_rule_source_found": False,
        "all_sources_filter_not_select": True,
        "noether_action_possible_but_not_supplied": True,
        "flrw_background_not_general_path_rule": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No indirect Janus source currently selects the cross-sector holonomy "
            "path rule. The audited structures are useful constraints, but none is "
            "a zero-axiom selector for L."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Indirect Path-Rule Source Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Audited source count: {payload['audited_source_count']}",
        f"Accepted indirect source count: {payload['accepted_indirect_source_count']}",
        f"Indirect path-rule source found: {payload['indirect_path_rule_source_found']}",
        f"All sources filter not select: {payload['all_sources_filter_not_select']}",
        f"Noether action possible but not supplied: {payload['noether_action_possible_but_not_supplied']}",
        f"FLRW background not general path rule: {payload['flrw_background_not_general_path_rule']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| source | could filter | selects path rule | blocker |",
        "|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['source']} | {row['could_filter']} | "
            f"{row['selects_path_rule']} | {row['blocker']} |"
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
