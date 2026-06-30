from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_external_janus_omega_source_search_gate.md")
JSON_PATH = Path("outputs/reports/p0_external_janus_omega_source_search_gate.json")


def build_payload() -> dict:
    evidence_targets = [
        {
            "target": "D_u L transport law",
            "search_for": "explicit Janus equation fixing D_u L or equivalent tetrad transport along u",
            "accept_if": "source-derived and implies Omega_u u=0 without gauge fitting",
            "reject_if": "only defines a convenient frame, ansatz, or local gauge choice",
        },
        {
            "target": "FW/comoving tetrad law",
            "search_for": "Fermi-Walker or comoving tetrad selection tied to Janus field/source equations",
            "accept_if": "the paper/site derives minimal rotation from source dynamics",
            "reject_if": "FW transport is imposed as convention or observer frame only",
        },
        {
            "target": "source congruence/cross-force",
            "search_for": "geodesic, congruence, or cross-force law that selects the shared source frame",
            "accept_if": "the same law cancels the Omega_u u residual for L transport",
            "reject_if": "force terms are phenomenological, optional, or unrelated to L/Omega",
        },
        {
            "target": "S_couple/Phi source",
            "search_for": "coupling action, Phi equation, or source measure deriving the transport law",
            "accept_if": "S_couple/Phi supplies the missing source closure with traceable equations",
            "reject_if": "it only motivates B_4vol, density measure, or potential notation",
        },
    ]
    rejection_rules = [
        "no closure from unsourced convention, frame choice, or post-residual gauge fit",
        "no prediction claim from analogy, terminology match, or partial source anchor",
        "no acceptance unless equations are externally citable and map to Omega_u u=0 / L transport",
        "reject claims that close only Phi, B_4vol, or source density without D_u L transport",
    ]
    return {
        "description": "Controlled external Janus source search gate for Omega_u u=0 / L transport.",
        "status": "external-janus-omega-source-search-gate-open",
        "scope": "artifact only; no browsing performed; no sourced closure claimed",
        "evidence_targets": evidence_targets,
        "target_count": len(evidence_targets),
        "acceptance_requires_external_source": True,
        "acceptance_requires_equation_trace": True,
        "acceptance_requires_omega_u_zero_transport": True,
        "acceptance_requires_no_gauge_fit": True,
        "rejection_rules": rejection_rules,
        "unsourced_closure_allowed": False,
        "external_search_performed": False,
        "external_janus_omega_source_search_results_available": True,
        "source_law_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "verdict": (
            "This gate only defines the bounded external search. Omega_u u=0 / L transport "
            "remains open until external Janus evidence source-derives the law; prediction is false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 External Janus Omega Source Search Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"External search performed: {payload['external_search_performed']}",
        f"External Janus omega source search results available: {payload['external_janus_omega_source_search_results_available']}",
        f"Source law found: {payload['source_law_found']}",
        f"Unsourced closure allowed: {payload['unsourced_closure_allowed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Evidence Targets",
        "",
        "| target | search for | accept if | reject if |",
        "|---|---|---|---|",
    ]
    for row in payload["evidence_targets"]:
        lines.append(
            "| {target} | {search_for} | {accept_if} | {reject_if} |".format(**row)
        )
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {rule}" for rule in payload["rejection_rules"])
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
