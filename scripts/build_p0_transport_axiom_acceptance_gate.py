from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_transport_axiom_acceptance_gate.md")
JSON_PATH = Path("outputs/reports/p0_transport_axiom_acceptance_gate.json")


def build_payload() -> dict:
    acceptance_criteria = [
        {
            "criterion": "source_derivation_exhausted",
            "requires": "Janus source/action equations fail to derive Omega_u u=0 after documented attempts",
            "passed": False,
        },
        {
            "criterion": "axiom_statement_complete",
            "requires": "explicit Lorentz transport law for the same L/Omega used by residuals, K, and Q_cross",
            "passed": True,
        },
        {
            "criterion": "mirror_consistency",
            "requires": "plus-to-minus and minus-to-plus transports are inverse mirror branches",
            "passed": True,
        },
        {
            "criterion": "dust_scope_locked",
            "requires": "rank-one dust closure is stated as the bounded scope; pressure/Pi remain open",
            "passed": True,
        },
        {
            "criterion": "no_rustine_compliance",
            "requires": "no fitted scalar patch, no independent optical map, no post-hoc Omega component choice",
            "passed": True,
        },
        {
            "criterion": "tested_before_acceptance",
            "requires": "focused report/test coverage proves the gate remains false until all criteria pass",
            "passed": True,
        },
    ]
    axiom_must_state = {
        "same_l_omega": "one L with Omega_alpha=(D_alpha L)L^{-1}; no separate L for residual, K, or Q_cross",
        "omega_u_zero": "Omega_u u=0 along the transported dust congruence, with Omega_u=u^alpha Omega_alpha",
        "mirror": "L_plus_to_minus=L_minus_to_plus^{-1} and mirrored Omega laws close both sectors consistently",
        "k_qcross": "K transport and Q_cross optical contractions consume the same fixed L/Omega",
        "dust_scope": "claim is bounded to rank-one dust unless a pressure/Pi extension is separately derived",
    }
    no_rustine_rules = [
        "do not accept an axiom because it removes the residual by notation",
        "do not tune Omega, L, K, or Q_cross from lensing/growth data",
        "do not introduce one transport map for K and another for Q_cross",
        "do not hide pressure, Pi, or non-comoving terms inside a scalar factor",
        "do not relabel a gauge convention as a Janus source derivation",
        "do not claim predictions while the explicit axiom is unaccepted or untested",
    ]
    decision_rules = [
        "If Omega_u u=0 is source-derived, no explicit transport axiom is required.",
        "If source derivation remains open, the explicit transport axiom is required before using the closure.",
        "If the explicit axiom is proposed but fails any criterion, keep it as research-only.",
        "Only after acceptance and tests can prediction_ready become true.",
    ]
    return {
        "description": (
            "Bounded P0 gate for deciding whether an explicit transport axiom is required "
            "when Janus sources do not derive Omega_u u=0."
        ),
        "status": "transport-axiom-acceptance-gate-open",
        "source_derivation_closed": False,
        "bounded_external_source_search_performed": True,
        "external_source_search_omega_transport_audit_available": True,
        "external_source_search_scouple_phi_audit_available": True,
        "du_l_omega_dynamic_derivation_attempt_available": True,
        "omega_source_no_go_axiom_boundary_available": True,
        "explicit_axiom_required_if_not_derived": True,
        "transport_axiom_candidate_statement_available": True,
        "explicit_axiom_written": True,
        "explicit_axiom_accepted": False,
        "accepted_and_tested": False,
        "rank_one_dust_scope": True,
        "pressure_pi_extension_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "acceptance_criteria": acceptance_criteria,
        "axiom_must_state": axiom_must_state,
        "no_rustine_rules": no_rustine_rules,
        "decision_rules": decision_rules,
        "verdict": (
            "The bounded source audits did not find a Janus-derived Omega_u u=0 law. "
            "A complete rank-one dust transport axiom candidate is written, but not "
            "accepted as physics: source exhaustion and residual closure remain open. "
            "Prediction remains false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Transport Axiom Acceptance Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derivation closed: {payload['source_derivation_closed']}",
        f"Bounded external source search performed: {payload['bounded_external_source_search_performed']}",
        "Omega transport audit available: "
        f"{payload['external_source_search_omega_transport_audit_available']}",
        "S_couple/Phi audit available: "
        f"{payload['external_source_search_scouple_phi_audit_available']}",
        "D_u L/Omega dynamic derivation attempt available: "
        f"{payload['du_l_omega_dynamic_derivation_attempt_available']}",
        "Omega source no-go axiom boundary available: "
        f"{payload['omega_source_no_go_axiom_boundary_available']}",
        f"Explicit axiom required if not derived: {payload['explicit_axiom_required_if_not_derived']}",
        f"Transport axiom candidate statement available: {payload['transport_axiom_candidate_statement_available']}",
        f"Explicit axiom written: {payload['explicit_axiom_written']}",
        f"Explicit axiom accepted: {payload['explicit_axiom_accepted']}",
        f"Accepted and tested: {payload['accepted_and_tested']}",
        f"Rank-one dust scope: {payload['rank_one_dust_scope']}",
        f"Pressure/Pi extension closed: {payload['pressure_pi_extension_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Acceptance Criteria",
        "",
        "| criterion | requires | passed |",
        "|---|---|---|",
    ]
    for row in payload["acceptance_criteria"]:
        lines.append(f"| {row['criterion']} | {row['requires']} | {row['passed']} |")
    lines.extend(["", "## Axiom Must State", ""])
    for key, value in payload["axiom_must_state"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## No-Rustine Rules", ""])
    lines.extend(f"- {item}" for item in payload["no_rustine_rules"])
    lines.extend(["", "## Decision Rules", ""])
    lines.extend(f"- {item}" for item in payload["decision_rules"])
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
