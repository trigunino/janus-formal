from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_source_omega_traceability_audit.md")
JSON_PATH = Path("outputs/reports/p0_janus_source_omega_traceability_audit.json")


def build_payload() -> dict:
    candidate_sources = [
        {
            "candidate": "M15/B_4vol field-source slot",
            "anchor": "M15 Eqs. 4a-4b determinant-weighted cross sources",
            "available_content": "selects B_4vol as active cross-source measure",
            "traceability_status": "partial-anchor",
            "blocker": "does not derive D_u L, Omega_u, or a flow law implying Omega_u u=0",
        },
        {
            "candidate": "pulled dust action",
            "anchor": "pulled dust EL/projection artifacts",
            "available_content": "rank-one dust stress and projected Cuu/Omega residual algebra",
            "traceability_status": "open",
            "blocker": "action-to-map variation has not produced the Omega source law",
        },
        {
            "candidate": "FW/comoving tetrad",
            "anchor": "Fermi-Walker minimal-rotation branch and comoving tetrad target",
            "available_content": "candidate transport condition that would make Omega_u u=0 along a dust flow",
            "traceability_status": "candidate-only",
            "blocker": "currently a gauge/transport candidate, not selected by Janus source equations",
        },
        {
            "candidate": "source congruence/cross-force",
            "anchor": "source congruence Omega gate and weak-congruence connection-force reduction",
            "available_content": "geodesic or covariant f_cross routes that could cancel the Omega_u u residual",
            "traceability_status": "route-open",
            "blocker": "neither u.Du=0 nor f_cross cancellation is source-derived for the shared L/Omega",
        },
    ]
    blockers = [
        "no existing local artifact derives a Janus source law for Omega_u u=0",
        "B_4vol is source-anchored as a measure, not as a transport equation for L/Omega",
        "pulled dust variation/projection remains conditional and does not close the map law",
        "FW/comoving tetrad and source-congruence routes remain candidate gates",
        "same L/Omega compatibility with K transport and Q_cross is still open",
    ]
    return {
        "description": "Bounded P0 audit of whether existing Janus/source artifacts derive Omega_u u=0.",
        "status": "source-omega-traceability-open",
        "scope": "traceability audit only; no new law and no prediction",
        "candidate_sources": candidate_sources,
        "blockers": blockers,
        "candidate_count": len(candidate_sources),
        "omega_u_zero_source_law_found": False,
        "b4vol_measure_anchor_found": True,
        "pulled_dust_action_derivation_closed": False,
        "fw_comoving_source_selected": False,
        "source_congruence_or_cross_force_closed": False,
        "same_l_omega_k_qcross_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "verdict": (
            "Existing artifacts identify plausible anchors and routes, but none supplies "
            "a source law deriving Omega_u u=0. The audit is therefore traceability-open "
            "and non-predictive."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Source Omega Traceability Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"Omega_u u=0 source law found: {payload['omega_u_zero_source_law_found']}",
        f"B4vol measure anchor found: {payload['b4vol_measure_anchor_found']}",
        f"Pulled dust action derivation closed: {payload['pulled_dust_action_derivation_closed']}",
        f"FW/comoving source selected: {payload['fw_comoving_source_selected']}",
        f"Source congruence/cross-force closed: {payload['source_congruence_or_cross_force_closed']}",
        f"Same L/Omega K/Q_cross closed: {payload['same_l_omega_k_qcross_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Candidate Sources",
        "",
        "| candidate | anchor | available content | traceability status | blocker |",
        "|---|---|---|---|---|",
    ]
    for row in payload["candidate_sources"]:
        lines.append(
            "| {candidate} | {anchor} | {available_content} | {traceability_status} | {blocker} |".format(
                **row
            )
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
