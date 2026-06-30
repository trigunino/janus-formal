from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_source_no_go_axiom_boundary.md")
JSON_PATH = Path("outputs/reports/p0_omega_source_no_go_axiom_boundary.json")


def build_payload() -> dict:
    boundary_rows = [
        {
            "case": "no_source_law",
            "premise": "current Janus source audits find no D_u L/Omega law",
            "boundary": "Omega_u u=0 remains gauge/candidate only",
            "allowed_claim": "no promotion to physics",
        },
        {
            "case": "explicit_axiom_acceptance",
            "premise": "Omega_u u=0 is adopted despite no source derivation",
            "boundary": "new explicit no-fit axiom",
            "allowed_claim": "rank-one dust scope only",
        },
        {
            "case": "outside_rank_one_dust",
            "premise": "pressure, Pi, multistream, or fitted closure is needed",
            "boundary": "not covered by the axiom",
            "allowed_claim": "pressure/Pi still open; no predictions",
        },
    ]
    return {
        "description": "Bounded P0 boundary after failed Janus source search for a D_u L/Omega law.",
        "status": "source-no-go-or-explicit-axiom-boundary",
        "scope": "conditional boundary only; no new prediction and no fitted closure",
        "source_audit_result": "no D_u L/Omega law found",
        "janus_source_audits_find_law": False,
        "omega_u_zero_source_derived": False,
        "without_source_law_promotes_to_physics": False,
        "omega_u_zero_without_source_status": "gauge/candidate",
        "explicit_axiom_available": True,
        "explicit_axiom_adopted_here": False,
        "if_adopted_is_new_axiom": True,
        "if_adopted_scope": "rank-one dust only",
        "rank_one_dust_scope_only": True,
        "pressure_pi_closed": False,
        "predictions_ready": False,
        "fitted_closure": False,
        "boundary_rows": boundary_rows,
        "verdict": (
            "No current Janus source audit derives a D_u L/Omega law. Therefore Omega_u u=0 "
            "cannot be promoted from gauge/candidate to physics unless it is adopted as a new "
            "explicit axiom, and that axiom has rank-one dust scope only."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Source No-Go Axiom Boundary",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"Source audit result: {payload['source_audit_result']}",
        f"Janus source audits find law: {payload['janus_source_audits_find_law']}",
        f"Omega_u u=0 source derived: {payload['omega_u_zero_source_derived']}",
        f"Without source law promotes to physics: {payload['without_source_law_promotes_to_physics']}",
        f"Omega_u u=0 without source status: {payload['omega_u_zero_without_source_status']}",
        f"Explicit axiom available: {payload['explicit_axiom_available']}",
        f"Explicit axiom adopted here: {payload['explicit_axiom_adopted_here']}",
        f"If adopted is new axiom: {payload['if_adopted_is_new_axiom']}",
        f"If adopted scope: {payload['if_adopted_scope']}",
        f"Rank-one dust scope only: {payload['rank_one_dust_scope_only']}",
        f"Pressure/Pi closed: {payload['pressure_pi_closed']}",
        f"Predictions ready: {payload['predictions_ready']}",
        f"Fitted closure: {payload['fitted_closure']}",
        "",
        "## Boundary Rows",
        "",
        "| case | premise | boundary | allowed claim |",
        "|---|---|---|---|",
    ]
    for row in payload["boundary_rows"]:
        lines.append("| {case} | {premise} | {boundary} | {allowed_claim} |".format(**row))
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
