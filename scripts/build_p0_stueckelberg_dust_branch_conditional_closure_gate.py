from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dust_branch_conditional_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dust_branch_conditional_closure_gate.json")


def build_payload() -> dict:
    gates = [
        {
            "id": "G1",
            "name": "projected_dust_variation_identity",
            "requirement": "map variation gives transverse divergence of transported dust stress",
            "status": "conditional-progress",
        },
        {
            "id": "G2",
            "name": "phi_l_convention_lock",
            "requirement": "same inverse phi pair and same L for K, velocities, and Q_cross",
            "status": "required-not-proved",
        },
        {
            "id": "G3",
            "name": "density_volume_consistency",
            "requirement": "B rho effective density convention closes D_phi/DlogB without double counting",
            "status": "conditional",
        },
        {
            "id": "G4",
            "name": "mirror_inverse_residual",
            "requirement": "minus residual is inverse-map mirror of plus residual",
            "status": "required-not-proved",
        },
        {
            "id": "G5",
            "name": "integrability_curls",
            "requirement": "curl obstruction vanishes on the transported dust image distribution",
            "status": "open",
        },
    ]
    verdict = {
        "dust_branch_status": "conditionally-fermable-not-closed",
        "can_advance_to_numerical_diagnostic": True,
        "can_claim_physical_prediction": False,
        "reason": (
            "The dust branch now has a real source-derived shape for the transverse "
            "connection residual, but closure still depends on convention, mirror, "
            "volume, and curl gates. It may support diagnostics, not final predictions."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_dust_branch_conditional_closure_gate",
        "status": "conditional-closure-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "gates": gates,
        "verdict": verdict,
    }


def render_markdown(payload: dict) -> str:
    verdict = payload["verdict"]
    lines = [
        "# P0 Stueckelberg Dust Branch Conditional Closure Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gates",
    ]
    for row in payload["gates"]:
        lines.append(f"- {row['id']} {row['name']}: {row['requirement']} (status={row['status']})")
    lines.extend(
        [
            "",
            "## Verdict",
            f"Dust branch status: {verdict['dust_branch_status']}",
            f"Can advance to numerical diagnostic: {verdict['can_advance_to_numerical_diagnostic']}",
            f"Can claim physical prediction: {verdict['can_claim_physical_prediction']}",
            f"Reason: {verdict['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
