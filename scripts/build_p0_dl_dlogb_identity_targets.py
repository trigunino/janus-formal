from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dl_dlogb_identity_targets.md")
JSON_PATH = Path("outputs/reports/p0_dl_dlogb_identity_targets.json")


def build_payload() -> dict:
    dl_targets = [
        {
            "identity": "D_alpha(L^T eta L)=0",
            "expanded": "(D_alpha L)^T eta L + L^T eta D_alpha L = 0",
            "needed_for": "Lorentz admissibility of K/Q_cross transport",
            "closed": False,
        },
        {
            "identity": "D_alpha L_minus_to_plus = F_alpha L_minus_to_plus",
            "expanded": "F_alpha^T eta + eta F_alpha = 0",
            "needed_for": "antisymmetric Lorentz-generator form of the transport law",
            "closed": False,
        },
        {
            "identity": "mirror consistency",
            "expanded": "D_alpha L_plus_to_minus = -L_plus_to_minus (D_alpha L_minus_to_plus) L_plus_to_minus",
            "needed_for": "same residual cancellation in plus and minus sectors",
            "closed": False,
        },
    ]
    dlogb_targets = [
        {
            "identity": "D_plus_alpha log B_4vol_plus_from_minus",
            "expanded": "1/2 D_plus_alpha log(-g_minus) - 1/2 D_plus_alpha log(-g_plus)",
            "needed_for": "field-equation measure product rule in R_plus",
            "closed": False,
        },
        {
            "identity": "D_minus_alpha log B_4vol_minus_from_plus",
            "expanded": "1/2 D_minus_alpha log(-g_plus) - 1/2 D_minus_alpha log(-g_minus)",
            "needed_for": "field-equation measure product rule in R_minus",
            "closed": False,
        },
        {
            "identity": "FLRW lapse split",
            "expanded": "D log B_4vol = D log N_other/N_self + 3 D log a_other/a_self + D log sqrt(gamma_other/gamma_self)",
            "needed_for": "separating lapse terms from dust 3-volume terms",
            "closed": False,
        },
    ]
    rejection_rules = [
        "reject D L=0 unless source equations prove parallel cross-transport",
        "reject B_4vol=V3_dust unless lapse and spatial determinant ratios are proved equivalent",
        "reject any residual cancellation using Q_cross as a source determinant",
        "reject numerical prediction while any identity row has closed=false",
    ]
    return {
        "description": "P0 identity targets for D L and D log B_4vol closure.",
        "status": "identity-targets-open",
        "dl_identities_written": True,
        "dlogb_identities_written": True,
        "all_identities_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "dl_targets": dl_targets,
        "dlogb_targets": dlogb_targets,
        "rejection_rules": rejection_rules,
        "verdict": (
            "The missing proof is now localized: D L must be a Lorentz-generator "
            "transport law, and D log B_4vol must retain lapse/measure terms. "
            "No closure follows until these identities are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 DL and DlogB Identity Targets",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All identities closed: {payload['all_identities_closed']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## D L Targets",
        "",
    ]
    for row in payload["dl_targets"]:
        lines.append(f"- `{row['identity']}`")
        lines.append(f"  - expanded: `{row['expanded']}`")
        lines.append(f"  - needed for: {row['needed_for']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## D log B Targets", ""])
    for row in payload["dlogb_targets"]:
        lines.append(f"- `{row['identity']}`")
        lines.append(f"  - expanded: `{row['expanded']}`")
        lines.append(f"  - needed for: {row['needed_for']}")
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
