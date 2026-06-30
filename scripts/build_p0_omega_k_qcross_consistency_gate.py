from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_k_qcross_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_omega_k_qcross_consistency_gate.json")


def build_payload() -> dict:
    consistency_rows = [
        {
            "gate": "shared_l_omega",
            "requirement": "K transport and Q_cross optical projection use the same L and Omega=(D L)L^{-1}",
            "closed": False,
        },
        {
            "gate": "no_k_only_cancellation",
            "requirement": "Omega may not be chosen only to cancel the K_plus/K_minus Bianchi residual",
            "closed": False,
        },
        {
            "gate": "mirror_inverse",
            "requirement": "L_plus_to_minus=L_minus_to_plus^{-1} or a source-derived mirror inverse with matching Omega",
            "closed": False,
        },
        {
            "gate": "optical_projection_compatibility",
            "requirement": "Q_cross contractions are induced by the same transported tetrads and photon covectors",
            "closed": False,
        },
    ]
    forbidden_shortcuts = [
        "do not choose Omega to cancel K transport only",
        "do not use a different L/Omega for Q_cross than for K_plus/K_minus",
        "do not repair mirror mismatch with scalar Q_cross or Q_det",
        "do not claim prediction before K residual and optical projection compatibility are both checked",
    ]
    prediction_requirements = [
        "same L/Omega fixed before residual substitution",
        "mirror inverse or source-derived mirror map proved",
        "K_plus and K_minus residual closure checked with that Omega",
        "Q_cross optical projection compatibility checked with that Omega",
    ]
    return {
        "description": "P0 gate requiring the Lorentz-gauge residual Omega to be shared by K transport and Q_cross.",
        "status": "omega-k-qcross-consistency-open",
        "same_l_omega_required": True,
        "k_only_omega_choice_allowed": False,
        "mirror_inverse_required": True,
        "optical_projection_compatibility_required": True,
        "consistency_rows_defined": True,
        "physics_closed": False,
        "prediction_ready": False,
        "consistency_rows": consistency_rows,
        "forbidden_shortcuts": forbidden_shortcuts,
        "prediction_requirements": prediction_requirements,
        "verdict": (
            "Omega is not a free K-residual cancellation knob. The same L/Omega "
            "structure must pass mirror-inverse and Q_cross optical projection "
            "compatibility before any prediction claim."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega/K/Q_cross Consistency Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Same L/Omega required: {payload['same_l_omega_required']}",
        f"K-only Omega choice allowed: {payload['k_only_omega_choice_allowed']}",
        f"Mirror inverse required: {payload['mirror_inverse_required']}",
        f"Optical projection compatibility required: {payload['optical_projection_compatibility_required']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| gate | requirement | closed |",
        "|---|---|---|",
    ]
    for row in payload["consistency_rows"]:
        lines.append(f"| {row['gate']} | {row['requirement']} | {row['closed']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Prediction Requirements", ""])
    lines.extend(f"- {item}" for item in payload["prediction_requirements"])
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
