from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_omega_projection_annihilation_gate.md")
JSON_PATH = Path("outputs/reports/p0_omega_projection_annihilation_gate.json")


def build_payload() -> dict:
    residual = "R_Omega=L(Omega^T T + T Omega)L^T"
    projection_condition = "P R_Omega P^T=0"
    gate_rows = [
        {
            "gate": "projection_condition",
            "requirement": f"define a source-derived projection P such that {projection_condition}",
            "closed": False,
        },
        {
            "gate": "shared_source_projection",
            "requirement": "same source-derived P must be used by K, Q_cross, and lensing observables",
            "closed": False,
        },
        {
            "gate": "no_observable_posthoc_projection",
            "requirement": "P cannot be chosen after seeing observables or fitted to cancel the residual",
            "closed": True,
        },
        {
            "gate": "prediction_claim",
            "requirement": "prediction remains false until P is fixed upstream and residual annihilation is proved",
            "closed": False,
        },
    ]
    forbidden_shortcuts = [
        "do not project observables after computing K/Q_cross/lensing",
        "do not fit P to make P R_Omega P^T vanish",
        "do not use different projections for source dynamics and optical observables",
    ]
    return {
        "artifact": "p0_omega_projection_annihilation_gate",
        "description": "Bounded P0 alternative: an observable/source projection annihilates the Omega residual.",
        "status": "omega-projection-annihilation-open",
        "omega_residual": residual,
        "projection_condition": projection_condition,
        "source_derived_projection_required": True,
        "shared_with_k": True,
        "shared_with_q_cross": True,
        "shared_with_lensing": True,
        "posthoc_observable_projection_allowed": False,
        "observable_fit_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "gate_rows": gate_rows,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "This is only a viable route if P is derived from the source construction "
            "before observable evaluation and the same P annihilates the Omega residual "
            "inside K, Q_cross, and lensing. No post-hoc observable projection or fit "
            "counts as a prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Projection Annihilation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Omega residual: {payload['omega_residual']}",
        f"Projection condition: {payload['projection_condition']}",
        f"Source-derived projection required: {payload['source_derived_projection_required']}",
        f"Shared with K: {payload['shared_with_k']}",
        f"Shared with Q_cross: {payload['shared_with_q_cross']}",
        f"Shared with lensing: {payload['shared_with_lensing']}",
        f"Post-hoc observable projection allowed: {payload['posthoc_observable_projection_allowed']}",
        f"Observable fit allowed: {payload['observable_fit_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| gate | requirement | closed |",
        "|---|---|---|",
    ]
    for row in payload["gate_rows"]:
        lines.append(f"| {row['gate']} | {row['requirement']} | {row['closed']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
