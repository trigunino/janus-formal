from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_effective_density_continuity_pullback_proof.md")
JSON_PATH = Path("outputs/reports/p0_effective_density_continuity_pullback_proof.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "id": "C1",
            "claim": "source dust action gives D_source(rho_source u_source)=0",
            "status": "standard-closed",
        },
        {
            "id": "C2",
            "claim": (
                "receiver effective current is the pulled vector density "
                "J_eff^mu = B_4vol rho_to u_to^mu"
            ),
            "status": "field-source-anchored-by-M15",
        },
        {
            "id": "C3",
            "claim": (
                "with B_4vol = phi^*sqrt|g_source| / sqrt|g_receiver| and "
                "u_to = phi_*u_source, receiver divergence commutes with pullback"
            ),
            "status": "mathematical-pullback-closed",
        },
        {
            "id": "C4",
            "claim": (
                "D_receiver(B_4vol rho_to u_to)= "
                "B_4vol phi^*(D_source(rho_source u_source)) = 0"
            ),
            "status": "closed-for-single-cross-dust-pullback",
        },
    ]
    forbidden_shortcuts = [
        "do not set B_4vol by fit",
        "do not replace B_4vol by dust 3-volume without lapse/slice proof",
        "do not absorb this continuity into Q_cross",
        "do not use the result for pressure/Pi matter",
    ]
    open_source_rows = [
        "phi/L map must be the same map used in the dust pullback and in Cuu",
        "mirror plus/minus inverse must satisfy the same vector-density identity",
        "pulled dust action must reproduce the same B_4vol field-source slot",
    ]
    return {
        "description": "Pullback proof target for effective dust continuity.",
        "status": "pullback-continuity-field-source-anchored",
        "target_identity": "D_receiver(B_4vol rho_to u_to)=0",
        "derivation_steps": derivation_steps,
        "forbidden_shortcuts": forbidden_shortcuts,
        "open_source_rows": open_source_rows,
        "standard_source_continuity_closed": True,
        "pullback_vector_density_theorem_closed": True,
        "janus_field_source_measure_anchored": True,
        "pulled_action_measure_anchored": False,
        "single_cross_dust_effective_continuity_closed": True,
        "effective_density_continuity_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The continuity identity is closed for a single pulled cross-dust current "
            "because M15 selects B_4vol in the active cross-source slot. The full "
            "Janus closure still needs the action/phi/L/mirror bridge."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Effective Density Continuity Pullback Proof",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target identity: `{payload['target_identity']}`",
        f"Source continuity closed: {payload['standard_source_continuity_closed']}",
        f"Pullback theorem closed: {payload['pullback_vector_density_theorem_closed']}",
        f"Janus field-source measure anchored: {payload['janus_field_source_measure_anchored']}",
        f"Pulled action measure anchored: {payload['pulled_action_measure_anchored']}",
        f"Single cross-dust effective continuity closed: {payload['single_cross_dust_effective_continuity_closed']}",
        f"Effective-density continuity closed: {payload['effective_density_continuity_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"- {row['id']}: {row['claim']} ({row['status']})")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Open Source Rows", ""])
    lines.extend(f"- {item}" for item in payload["open_source_rows"])
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
