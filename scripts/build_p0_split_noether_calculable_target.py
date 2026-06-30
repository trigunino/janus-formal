from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_split_noether_calculable_target.md")
JSON_PATH = Path("outputs/reports/p0_split_noether_calculable_target.json")


def build_payload() -> dict:
    objects = [
        {
            "object": "K_plus",
            "definition": "-2/sqrt(-g_plus) delta S_couple/delta g_plus",
            "status": "symbolic-target",
        },
        {
            "object": "K_minus",
            "definition": "-2/sqrt(-g_minus) delta S_couple/delta g_minus",
            "status": "symbolic-target",
        },
        {
            "object": "E_phi",
            "definition": "delta S_couple/delta phi",
            "status": "symbolic-target",
        },
        {
            "object": "E_L",
            "definition": "delta S_couple/delta L",
            "status": "symbolic-target",
        },
    ]
    identities = [
        {
            "identity": "R_plus = D_plus(T_plus + K_plus) + E_phi dot D_plus(phi) + E_L dot D_plus(L)",
            "closed_on_shell_if": "E_phi=0 and E_L=0 and plus diffeo identity is independently restored",
            "proved": False,
        },
        {
            "identity": "R_minus = D_minus(T_minus + K_minus) + E_phi_bar dot D_minus(phi_inverse) + E_L_bar dot D_minus(L_inverse)",
            "closed_on_shell_if": "mirror E_phi_bar=0 and E_L_bar=0 and minus diffeo identity is independently restored",
            "proved": False,
        },
    ]
    calculable_steps = [
        "choose a bounded Phi candidate",
        "compute K_plus/K_minus by metric variation",
        "compute E_phi/E_L by map variation",
        "substitute into R_plus/R_minus",
        "solve coefficient equations for candidate constants",
        "reject candidate if residual leaves nonzero tensor terms",
    ]
    return {
        "description": "Calculable target for replacing model Noether constraints with split Noether residual identities.",
        "status": "split-noether-calculable-target-open",
        "objects": objects,
        "identities": identities,
        "calculable_steps": calculable_steps,
        "replaces_noether_like_constraints": True,
        "split_noether_identities_written": True,
        "split_noether_identities_proved": False,
        "can_eliminate_phi_family_now": False,
        "requires_candidate_phi": True,
        "linear_phi_candidate_available": True,
        "linear_imatter_tensor_contract_available": True,
        "linear_imatter_metric_variation_available": True,
        "linear_imatter_stress_response_target_available": True,
        "linear_imatter_l_variation_available": True,
        "linear_imatter_lorentz_projected_el_available": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This makes the real Split Noether task calculable. It does not yet prove the "
            "identities or eliminate the Phi family; a concrete Phi candidate must be varied "
            "and substituted."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Split Noether Calculable Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Replaces Noether-like constraints: {payload['replaces_noether_like_constraints']}",
        f"Split Noether identities written: {payload['split_noether_identities_written']}",
        f"Split Noether identities proved: {payload['split_noether_identities_proved']}",
        f"Can eliminate Phi family now: {payload['can_eliminate_phi_family_now']}",
        f"Linear Phi candidate available: {payload['linear_phi_candidate_available']}",
        f"Linear I_matter tensor contract available: {payload['linear_imatter_tensor_contract_available']}",
        f"Linear I_matter metric variation available: {payload['linear_imatter_metric_variation_available']}",
        f"Linear I_matter stress response target available: {payload['linear_imatter_stress_response_target_available']}",
        f"Linear I_matter L variation available: {payload['linear_imatter_l_variation_available']}",
        f"Linear I_matter Lorentz-projected E_L available: {payload['linear_imatter_lorentz_projected_el_available']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Objects",
        "",
    ]
    for row in payload["objects"]:
        lines.append(f"- {row['object']}: `{row['definition']}` ({row['status']})")
    lines.extend(["", "## Identities", ""])
    for row in payload["identities"]:
        lines.append(f"- `{row['identity']}`")
        lines.append(f"  - closed on shell if: {row['closed_on_shell_if']}")
        lines.append(f"  - proved: {row['proved']}")
    lines.extend(["", "## Calculable Steps", ""])
    lines.extend(f"- {item}" for item in payload["calculable_steps"])
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
