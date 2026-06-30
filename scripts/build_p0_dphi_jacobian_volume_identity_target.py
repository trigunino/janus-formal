from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dphi_jacobian_volume_identity_target.md")
JSON_PATH = Path("outputs/reports/p0_dphi_jacobian_volume_identity_target.json")


def build_payload() -> dict:
    identities = [
        {
            "id": "J1",
            "identity": "sqrt|g_plus| J_phi = phi^* sqrt|g_minus|",
            "role": "turn pulled density into a true volume-density pullback",
            "closed": False,
        },
        {
            "id": "J2",
            "identity": "L_u(J_phi phi^*rho)=J_phi phi^*(L_{phi_*u} rho)+rho_to L_u log J_phi",
            "role": "separate density Lie derivative from Jacobian divergence",
            "closed": False,
        },
        {
            "id": "J3",
            "identity": "D log B = D log J_phi + transported metric-volume remainder",
            "role": "connect D_phi density cancellation to DlogB volume cancellation",
            "closed": False,
        },
        {
            "id": "J4",
            "identity": "D_receiver(B rho_to u_to)=0 iff transported source continuity plus J1-J3",
            "role": "close the effective-density continuity row used by the EL projection",
            "closed": False,
        },
    ]
    rejection_rules = [
        "do not set J_phi=1 unless the map is proven volume-preserving on the support",
        "do not identify dust 3-volume ratio with B_4vol without lapse accounting",
        "do not multiply by Q_det twice after choosing B rho as effective density",
        "do not use Q_cross to cancel a density-measure term",
    ]
    return {
        "description": "Target identities for D_phi Jacobian/volume cancellation in pulled dust.",
        "status": "jacobian-volume-identity-target-open",
        "identities": identities,
        "rejection_rules": rejection_rules,
        "dphi_measure_identity_written": True,
        "all_identities_closed": False,
        "effective_density_continuity_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "D_phi density cancellation is reduced to four explicit Jacobian/volume "
            "identities. They are not closed, but the proof obligation is now finite."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 D_phi Jacobian Volume Identity Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"D_phi measure identity written: {payload['dphi_measure_identity_written']}",
        f"All identities closed: {payload['all_identities_closed']}",
        f"Effective-density continuity closed: {payload['effective_density_continuity_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
    ]
    for row in payload["identities"]:
        lines.append(f"- {row['id']}: `{row['identity']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
