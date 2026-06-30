from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_same_phi_l_cuu_bridge.md")
JSON_PATH = Path("outputs/reports/p0_same_phi_l_cuu_bridge.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "id": "P1",
            "claim": "one declared phi/L pushes source dust velocity v to receiver velocity u_to",
            "formula": "u_to = phi_* v, with tetrad representation fixed by the same L",
            "closed": True,
        },
        {
            "id": "P2",
            "claim": "covariant acceleration transport splits into source acceleration plus connection difference",
            "formula": "u_to^alpha D_to_alpha u_to^mu = phi_*(v^a D_source_a v)^mu + C^mu_{alpha beta} u_to^alpha u_to^beta",
            "closed": True,
        },
        {
            "id": "P3",
            "claim": "Janus sector matter follows its own metric geodesics",
            "formula": "v^a D_source_a v^b = 0",
            "closed": True,
        },
        {
            "id": "P4",
            "claim": "therefore the transported dust force is the projected Cuu force",
            "formula": "h a_to = h C(u_to,u_to)",
            "closed": True,
        },
    ]
    remaining_rows = [
        "prove the same phi/L pair is selected dynamically by Janus action equations",
        "prove plus/minus inverse-map mirror consistency",
        "prove no curl/integrability obstruction on the dust image support",
        "extend separately to pressure/Pi before tensor-matter closure",
    ]
    return {
        "description": "Same-map bridge from pulled dust geodesics to the projected Cuu force.",
        "status": "same-phi-l-cuu-bridge-closed-dynamic-selection-open",
        "target_identity": "h a_to = h C(u_to,u_to)",
        "derivation_steps": derivation_steps,
        "remaining_rows": remaining_rows,
        "same_phi_l_bridge_closed": True,
        "source_geodesic_anchor_closed": True,
        "single_cross_dust_cuu_force_closed": True,
        "dynamic_phi_l_selection_closed": False,
        "mirror_consistency_closed": False,
        "full_two_sector_bianchi_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "For a declared single phi/L pullback, source geodesic dust gives h a_to=h Cuu. "
            "This closes the local dust bridge, but not dynamic phi/L selection or mirror closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Same Phi/L Cuu Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target identity: `{payload['target_identity']}`",
        f"Same phi/L bridge closed: {payload['same_phi_l_bridge_closed']}",
        f"Source geodesic anchor closed: {payload['source_geodesic_anchor_closed']}",
        f"Single cross-dust Cuu force closed: {payload['single_cross_dust_cuu_force_closed']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror consistency closed: {payload['mirror_consistency_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"- {row['id']}: {row['claim']}")
        lines.append(f"  - formula: `{row['formula']}`")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Remaining Rows", ""])
    lines.extend(f"- {item}" for item in payload["remaining_rows"])
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
