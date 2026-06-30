from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_weak_selector_action_origin_audit.md")
JSON_PATH = Path("outputs/reports/p0_janus_weak_selector_action_origin_audit.json")


def build_payload() -> dict:
    action_rows = [
        {
            "action": "passive_source_dust_pullback",
            "formula": "S_o[g_o,rho_o,u_o] rewritten with phi",
            "variation_result": "Noether/boundary identity after source dust EL",
            "derives_weak_selector": False,
            "accepted_without_new_axiom": True,
        },
        {
            "action": "active_receiver_cross_dust",
            "formula": "S_x=int dmu_self B_4vol L_matter(g_self, phi_*rho_o, phi_*u_o)",
            "variation_result": "delta_phi S_x = -int dmu_self xi_nu nabla_self_mu T_to_self^{mu nu}",
            "derives_weak_selector": True,
            "accepted_without_new_axiom": False,
        },
        {
            "action": "weak_congruence_multiplier",
            "formula": "int lambda_mu h^mu_nu C^nu(u,u)",
            "variation_result": "imposes the target directly",
            "derives_weak_selector": True,
            "accepted_without_new_axiom": False,
        },
        {
            "action": "sourced_gl_strain",
            "formula": "S_strain[g_self,phi^*g_other,L]",
            "variation_result": "could select relative strain/L if source and stability are proved",
            "derives_weak_selector": "possible",
            "accepted_without_new_axiom": False,
        },
    ]
    derivation_rows = [
        {
            "row": "diffeomorphism_variation",
            "formula": "delta_phi S_x[xi] = -int sqrt|g| xi_nu nabla_mu T_to_self^{mu nu}+boundary",
            "closed": True,
        },
        {
            "row": "dust_stress",
            "formula": "T_to_self^{mu nu}=B_4vol rho_to u_to^mu u_to^nu",
            "closed": True,
        },
        {
            "row": "continuity_split",
            "formula": "nabla_mu(B_4vol rho_to u_to^mu)=0 removes longitudinal part",
            "closed": True,
        },
        {
            "row": "projected_el",
            "formula": "h^alpha_nu nabla_mu T^{mu nu}=B_4vol rho_to h^alpha_nu C^nu(u_to,u_to)",
            "closed": True,
        },
        {
            "row": "janus_source_acceptance",
            "formula": "published/source Janus must identify S_x as the cross-source action",
            "closed": False,
        },
    ]
    return {
        "description": "Action-origin audit for deriving the weak congruence selector without rustine.",
        "status": "active-cross-action-derives-selector-source-acceptance-open",
        "action_rows": action_rows,
        "derivation_rows": derivation_rows,
        "passive_pullback_insufficient": True,
        "active_cross_dust_action_derives_weak_selector": True,
        "weak_selector_derivation_shape_closed": True,
        "active_cross_action_source_accepted": False,
        "active_cross_action_acceptance_artifact": "p0_janus_active_cross_action_acceptance_gate",
        "multiplier_route_rejected_as_rustine": True,
        "gl_strain_route_requires_source_stability": True,
        "weak_selector_action_origin_closed": False,
        "new_axiom_if_adopted_without_janus_source": True,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The weak selector is derivable from an active receiver-coupled cross-dust action, "
            "not from a passive source-dust pullback alone. The derivation shape is closed; "
            "the remaining blocker is Janus source acceptance of that active cross action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak Selector Action Origin Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Passive pullback insufficient: {payload['passive_pullback_insufficient']}",
        f"Active cross dust action derives weak selector: {payload['active_cross_dust_action_derives_weak_selector']}",
        f"Weak selector derivation shape closed: {payload['weak_selector_derivation_shape_closed']}",
        f"Active cross action source accepted: {payload['active_cross_action_source_accepted']}",
        "Active cross action acceptance artifact: "
        f"`{payload['active_cross_action_acceptance_artifact']}`",
        f"Multiplier route rejected as rustine: {payload['multiplier_route_rejected_as_rustine']}",
        f"Weak selector action origin closed: {payload['weak_selector_action_origin_closed']}",
        f"New axiom if adopted without Janus source: {payload['new_axiom_if_adopted_without_janus_source']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Action Rows",
        "",
        "| action | formula | variation result | derives selector | accepted without new axiom |",
        "|---|---|---|---:|---:|",
    ]
    for row in payload["action_rows"]:
        lines.append(
            f"| {row['action']} | `{row['formula']}` | {row['variation_result']} | "
            f"{row['derives_weak_selector']} | {row['accepted_without_new_axiom']} |"
        )
    lines.extend(
        [
            "",
            "## Derivation Rows",
            "",
            "| row | formula | closed |",
            "|---|---|---:|",
        ]
    )
    for row in payload["derivation_rows"]:
        lines.append(f"| {row['row']} | `{row['formula']}` | {row['closed']} |")
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
