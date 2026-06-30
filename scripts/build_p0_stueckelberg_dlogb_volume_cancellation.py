from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dlogb_volume_cancellation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dlogb_volume_cancellation.json")


def build_payload() -> dict:
    identities = [
        {
            "name": "density_measure_absorption",
            "equation": "D_plus(B_minus_to_plus rho_minus_to_plus)=B_minus_to_plus(D_phi rho_minus + rho_minus D_plus log B_minus_to_plus)",
            "effect": "can combine D_phi density and DlogB terms into one transported effective-density divergence",
            "closed": "conditional",
        },
        {
            "name": "mirror_density_measure_absorption",
            "equation": "D_minus(B_plus_to_minus rho_plus_to_minus)=B_plus_to_minus(D_phi rho_plus + rho_plus D_minus log B_plus_to_minus)",
            "effect": "mirror combination for R_minus",
            "closed": "conditional",
        },
    ]
    conditions = [
        "B is used as density/volume measure only",
        "Q_cross remains a separate optical projection factor",
        "the effective transported density satisfies continuity in the receiver sector",
        "no extra multiplication by B after choosing effective density convention",
    ]
    return {
        "description": "DlogB volume-gradient cancellation test for zero-parameter Stueckelberg dust.",
        "status": "dlogb-volume-cancellation-conditional",
        "dlogb_absorbable_into_effective_density": True,
        "closes_density_part_conditionally": True,
        "closes_full_residual": False,
        "qdet_qcross_separate": True,
        "physics_closed": False,
        "prediction_ready": False,
        "identities": identities,
        "conditions": conditions,
        "remaining_after_absorption": [
            "D_L transported velocity/tetrad terms",
            "connection difference force terms",
            "proof of transported effective-density continuity",
        ],
        "verdict": (
            "DlogB is not an independent fatal term if B*rho is treated as the transported "
            "effective density. This conditionally merges D_phi and DlogB. Full closure "
            "still needs D_L and connection-force cancellation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg DlogB Volume Cancellation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"DlogB absorbable into effective density: {payload['dlogb_absorbable_into_effective_density']}",
        f"Closes density part conditionally: {payload['closes_density_part_conditionally']}",
        f"Closes full residual: {payload['closes_full_residual']}",
        f"Q_det/Q_cross separate: {payload['qdet_qcross_separate']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
    ]
    for row in payload["identities"]:
        lines.append(f"- {row['name']}: `{row['equation']}`")
        lines.append(f"  - effect: {row['effect']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Conditions", ""])
    lines.extend(f"- {item}" for item in payload["conditions"])
    lines.extend(["", "## Remaining After Absorption", ""])
    lines.extend(f"- {item}" for item in payload["remaining_after_absorption"])
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
