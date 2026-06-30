from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_same_phi_l_cuu_bridge import build_payload as build_same_phi_l_bridge
from scripts.build_p0_cuu_jacobian_curl_numeric_probe import build_payload as build_jacobian_curl_probe


REPORT_PATH = Path("outputs/reports/p0_cuu_inverse_map_integrability_target.md")
JSON_PATH = Path("outputs/reports/p0_cuu_inverse_map_integrability_target.json")


def build_payload() -> dict:
    bridge = build_same_phi_l_bridge()
    curl_probe = build_jacobian_curl_probe()
    identities = [
        {
            "id": "CINV-1",
            "name": "inverse_connection_difference",
            "formula": "C_minus^a_bc = - (J^-1)^a_mu J^alpha_b J^beta_c C_plus^mu_alpha_beta",
            "requires": "one invertible phi with J=dphi",
            "closed": bridge["mirror_consistency_closed"],
        },
        {
            "id": "CINV-2",
            "name": "projected_force_mirror",
            "formula": "h_minus C_minus(u_plus_to_minus,u_plus_to_minus) mirrors h_plus C_plus(u_minus_to_plus,u_minus_to_plus)",
            "requires": "inverse phi/L and mirrored projectors",
            "closed": bridge["mirror_consistency_closed"],
        },
        {
            "id": "CINT-1",
            "name": "tetrad_l_to_jacobian",
            "formula": "J^mu_a = e_plus^mu_A L^A_B e_minus^B_a",
            "requires": "same Lorentz L used by Cuu, K transport, Q_cross, and kinetics",
            "closed": bridge["same_phi_l_bridge_closed"],
        },
        {
            "id": "CINT-2",
            "name": "phi_integrability",
            "formula": "partial_[a J^mu_b] = 0 on transported dust support",
            "requires": "candidate J is a Jacobian, not only pointwise tetrad algebra",
            "closed": bridge["dynamic_phi_l_selection_closed"],
        },
        {
            "id": "CINT-3",
            "name": "jacobian_curl_numeric_gate",
            "formula": "numeric dJ=0 gate rejects pointwise J defects",
            "requires": "source-selected J must pass the same curl gate as a true dphi",
            "closed": False,
        },
    ]
    forbidden_shortcuts = [
        "do not choose independent plus/minus C tensors",
        "do not promote pointwise L to a map phi without the Jacobian curl test",
        "do not close mirror Cuu by sign choice only",
        "do not use this dust identity for pressure/Pi transport",
    ]
    return {
        "description": "Inverse-map and integrability target for the projected Cuu physical blocker.",
        "status": "cuu-inverse-map-integrability-target-open",
        "depends_on": [
            "p0_same_phi_l_cuu_bridge",
            "p0_cuu_jacobian_curl_numeric_probe",
        ],
        "numeric_probe": "p0_cuu_jacobian_curl_numeric_probe",
        "identities": identities,
        "forbidden_shortcuts": forbidden_shortcuts,
        "single_cross_dust_bridge_closed": bridge["single_cross_dust_cuu_force_closed"],
        "inverse_c_relation_written": True,
        "jacobian_from_same_l_written": True,
        "jacobian_curl_numeric_probe_available": True,
        "compatible_jacobian_curl_closes": curl_probe["compatible_jacobian_curl_closes"],
        "curl_defected_jacobian_curl_closes": curl_probe["curl_defected_jacobian_curl_closes"],
        "mirror_inverse_closed": all(row["closed"] for row in identities if row["id"].startswith("CINV")),
        "integrability_closed": all(row["closed"] for row in identities if row["id"].startswith("CINT")),
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The inverse C relation and phi integrability test are now explicit. "
            "They remain open until Janus selects an invertible phi/L whose Jacobian curl vanishes."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Cuu Inverse Map Integrability Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Single-cross dust bridge closed: {payload['single_cross_dust_bridge_closed']}",
        f"Inverse C relation written: {payload['inverse_c_relation_written']}",
        f"Jacobian from same L written: {payload['jacobian_from_same_l_written']}",
        f"Jacobian curl numeric probe available: {payload['jacobian_curl_numeric_probe_available']}",
        f"Compatible Jacobian curl closes: {payload['compatible_jacobian_curl_closes']}",
        f"Curl-defected Jacobian curl closes: {payload['curl_defected_jacobian_curl_closes']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"Integrability closed: {payload['integrability_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        "| id | name | formula | requires | closed |",
        "|---|---|---|---|---:|",
    ]
    for row in payload["identities"]:
        lines.append(
            f"| {row['id']} | {row['name']} | `{row['formula']}` | "
            f"{row['requires']} | {row['closed']} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
