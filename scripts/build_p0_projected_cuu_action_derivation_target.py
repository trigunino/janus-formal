from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_projected_cuu_action_derivation_target.md")
JSON_PATH = Path("outputs/reports/p0_projected_cuu_action_derivation_target.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "step": "pullback_dust_action",
            "target": "write S_dust_minus_to_plus[phi,L,g_plus,g_minus,rho_minus,u_minus]",
            "closed": False,
        },
        {
            "step": "vary_phi_l",
            "target": "compute delta_phi,L S and isolate transverse E_phi/E_L projection",
            "closed": False,
        },
        {
            "step": "recover_connection_force",
            "target": "show projected variation equals rho h C(u,u), not an imposed constraint",
            "closed": False,
        },
        {
            "step": "mirror_consistency",
            "target": "derive plus and minus identities from inverse phi/L, not separate maps",
            "closed": False,
        },
        {
            "step": "integrability",
            "target": "show curl obstruction vanishes on the transported dust image",
            "closed": False,
        },
    ]
    sufficient_for_conditional_dust_closure = [
        "all derivation steps closed",
        "same L used by K transport and Q_cross",
        "DlogB measure convention matches density pullback",
        "pressure/Pi explicitly excluded or extended",
    ]
    return {
        "description": "Action-derivation target for the projected Cuu map-force identity.",
        "status": "action-derivation-target-open",
        "derivation_steps": derivation_steps,
        "sufficient_for_conditional_dust_closure": sufficient_for_conditional_dust_closure,
        "projected_cuu_identity_derived": False,
        "pulled_dust_action_weak_congruence_artifact": "p0_janus_pulled_dust_action_weak_congruence_proof",
        "mirror_consistency_closed": False,
        "integrability_closed": False,
        "conditional_dust_closure_ready": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the current shortest path to real progress: derive the projected "
            "Cuu force from the pulled dust action. Until then, weak congruence remains conditional."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Projected Cuu Action Derivation Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Projected Cuu identity derived: {payload['projected_cuu_identity_derived']}",
        "Pulled dust action weak congruence artifact: "
        f"`{payload['pulled_dust_action_weak_congruence_artifact']}`",
        f"Conditional dust closure ready: {payload['conditional_dust_closure_ready']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"- {row['step']}: {row['target']} (closed={row['closed']})")
    lines.extend(["", "## Sufficient For Conditional Dust Closure", ""])
    lines.extend(f"- {item}" for item in payload["sufficient_for_conditional_dust_closure"])
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
