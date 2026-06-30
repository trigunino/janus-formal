from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_effective_density_continuity_pullback_proof import (
    build_payload as build_continuity,
)
from scripts.build_p0_janus_weak_congruence_selector_derivation_gate import (
    build_payload as build_weak_selector,
)
from scripts.build_p0_janus_weak_selector_action_origin_audit import (
    build_payload as build_action_origin,
)
from scripts.build_p0_pulled_particle_action_cuu_derivation import (
    build_payload as build_particle_action,
)


REPORT_PATH = Path("outputs/reports/p0_janus_pulled_dust_action_weak_congruence_proof.md")
JSON_PATH = Path("outputs/reports/p0_janus_pulled_dust_action_weak_congruence_proof.json")


def build_payload() -> dict:
    particle = build_particle_action()
    continuity = build_continuity()
    weak_selector = build_weak_selector()
    action_origin = build_action_origin()
    proof_rows = [
        {
            "row": "particle_to_geodesic",
            "formula": "delta S_particle -> u^nu nabla_nu u^mu=0",
            "closed": bool(particle["particle_geodesic_variation_closed"]),
        },
        {
            "row": "cold_dust_lift",
            "formula": "monoflux dust integrates particle EL with density rho",
            "closed": bool(particle["cold_dust_lift_closed"]),
        },
        {
            "row": "pullback_continuity",
            "formula": "D_self(B_4vol rho_to u_to)=0",
            "closed": bool(continuity["single_cross_dust_effective_continuity_closed"]),
        },
        {
            "row": "projected_connection_difference",
            "formula": "h a_to = h C_self-other(u_to,u_to)",
            "closed": bool(particle["connection_difference_cross_pullback_closed"]),
        },
        {
            "row": "weak_congruence_target",
            "formula": "h E_phi/E_L = rho h C(u_to,u_to)",
            "closed": bool(weak_selector["weak_selector_equation_written"]),
        },
        {
            "row": "action_origin_for_selector",
            "formula": "weak selector follows from Janus E_phi/E_L, not an imposed multiplier",
            "closed": bool(action_origin["weak_selector_action_origin_closed"]),
        },
        {
            "row": "mirror_inverse",
            "formula": "minus proof is inverse-map image of plus proof",
            "closed": False,
        },
        {
            "row": "pressure_pi_extension",
            "formula": "pressure/Pi projected terms are transported or explicitly excluded",
            "closed": False,
        },
    ]
    closed_rows = [row["row"] for row in proof_rows if row["closed"]]
    open_rows = [row["row"] for row in proof_rows if not row["closed"]]
    return {
        "description": "Pulled dust action proof state for the weak congruence selector.",
        "status": "pulled-dust-action-proof-conditional-action-origin-open",
        "depends_on": [
            "p0_pulled_particle_action_cuu_derivation",
            "p0_effective_density_continuity_pullback_proof",
            "p0_janus_weak_congruence_selector_derivation_gate",
            "p0_janus_weak_selector_action_origin_audit",
        ],
        "proof_rows": proof_rows,
        "closed_rows": closed_rows,
        "open_rows": open_rows,
        "standard_dust_variation_closed": True,
        "single_cross_pullback_dust_closed": True,
        "projected_cuu_target_reached": True,
        "weak_selector_action_origin_artifact": "p0_janus_weak_selector_action_origin_audit",
        "active_cross_dust_action_derives_weak_selector": bool(
            action_origin["active_cross_dust_action_derives_weak_selector"]
        ),
        "action_origin_for_weak_selector_closed": bool(
            action_origin["weak_selector_action_origin_closed"]
        ),
        "new_axiom_if_adopted_without_janus_source": bool(
            action_origin["new_axiom_if_adopted_without_janus_source"]
        ),
        "mirror_inverse_closed": False,
        "pressure_pi_extension_closed": False,
        "conditional_dust_closure_ready": False,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The pulled dust action chain reaches the weak congruence target for a single "
            "cross-dust current. It is still conditional: the weak selector itself must be "
            "derived from Janus E_phi/E_L, then mirrored and extended or restricted for non-dust matter."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Pulled Dust Action Weak Congruence Proof",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Standard dust variation closed: {payload['standard_dust_variation_closed']}",
        f"Single cross pullback dust closed: {payload['single_cross_pullback_dust_closed']}",
        f"Projected Cuu target reached: {payload['projected_cuu_target_reached']}",
        f"Weak selector action origin artifact: `{payload['weak_selector_action_origin_artifact']}`",
        "Active cross dust action derives weak selector: "
        f"{payload['active_cross_dust_action_derives_weak_selector']}",
        f"Action origin for weak selector closed: {payload['action_origin_for_weak_selector_closed']}",
        "New axiom if adopted without Janus source: "
        f"{payload['new_axiom_if_adopted_without_janus_source']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"Pressure/Pi extension closed: {payload['pressure_pi_extension_closed']}",
        f"Conditional dust closure ready: {payload['conditional_dust_closure_ready']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Proof Rows",
        "",
        "| row | formula | closed |",
        "|---|---|---:|",
    ]
    for row in payload["proof_rows"]:
        lines.append(f"| {row['row']} | `{row['formula']}` | {row['closed']} |")
    lines.extend(
        [
            "",
            f"Closed rows: `{payload['closed_rows']}`",
            f"Open rows: `{payload['open_rows']}`",
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
