from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_dust_rank_one_condition.md")
JSON_PATH = Path("outputs/reports/p0_omega_dust_rank_one_condition.json")


def build_payload() -> dict:
    algebra = {
        "stress": "T=rho u u",
        "omega_residual": "Delta_Omega M = L(Omega^T T + T Omega)L^T",
        "rank_one_substitution": "Omega^T T + T Omega = rho[(Omega u)_flat u_flat + u_flat (Omega u)_flat]",
        "zero_condition": "for rho != 0 and timelike normalized u, residual zero requires Omega u parallel u and Lorentz-skew also gives u.Omega u=0, hence Omega u=0",
        "orthogonal_warning": "Omega u perpendicular u, equivalently orthogonal to u, is necessary for a Lorentz generator but is not sufficient; it leaves cross rank-two terms unless Omega u=0 or the observable projection kills them",
        "harmless_projection_condition": "harmless only after a source-derived projection/kernel proves P L[(Omega^T T+T Omega)]L^T P^T=0",
    }
    closure_requirements = [
        "Omega u=0 along the dust congruence, or a proved projection that annihilates the induced cross term",
        "the condition must be imposed on the same L used to induce K_plus/K_minus",
        "the same L/Omega data must feed Q_cross optical contractions",
        "no post-hoc fit may choose transverse/boost Omega components to cancel lensing residuals",
        "rho, u, L, K, and Q_cross must share one source-derived transport structure",
    ]
    blocked_shortcuts = [
        "treating Lorentz orthogonality Omega u perpendicular u as residual closure",
        "absorbing Omega u cross terms into a scalar density or scalar Q_cross",
        "choosing Omega from survey fit after K and Q_cross are built",
        "using one L for Bianchi K transport and another for optical Q_cross",
    ]
    return {
        "description": "Bounded P0 artifact isolating the Lorentz-gauge Omega residual for rank-one dust stress.",
        "status": "rank-one-condition-fails-prediction",
        "rank_one_substitution_done": True,
        "omega_u_parallel_required": True,
        "lorentz_orthogonal_only_insufficient": True,
        "timelike_parallel_forces_omega_u_zero": True,
        "fit_choice_allowed": False,
        "shared_with_k_qcross_required": True,
        "residual_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "algebra": algebra,
        "closure_requirements": closure_requirements,
        "blocked_shortcuts": blocked_shortcuts,
        "verdict": (
            "For dust T=rho u u, the Omega residual is not free gauge noise. "
            "Lorentz skew gives Omega u perpendicular u, but closure requires the stronger "
            "parallel condition; for timelike normalized u this means Omega u=0, unless a "
            "source-derived projection proves the cross term harmless. This condition must "
            "be shared with K and Q_cross, so the prediction claim is false."
        ),
    }


def render_markdown(payload: dict) -> str:
    a = payload["algebra"]
    lines = [
        "# P0 Omega Dust Rank-One Condition",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Rank-one substitution done: {payload['rank_one_substitution_done']}",
        f"Omega u parallel required: {payload['omega_u_parallel_required']}",
        f"Lorentz orthogonal only insufficient: {payload['lorentz_orthogonal_only_insufficient']}",
        f"Timelike parallel forces Omega u zero: {payload['timelike_parallel_forces_omega_u_zero']}",
        f"Fit choice allowed: {payload['fit_choice_allowed']}",
        f"Shared with K/Q_cross required: {payload['shared_with_k_qcross_required']}",
        f"Residual closed: {payload['residual_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Algebra",
        "",
        f"- stress: `{a['stress']}`",
        f"- omega residual: `{a['omega_residual']}`",
        f"- rank-one substitution: `{a['rank_one_substitution']}`",
        f"- zero condition: {a['zero_condition']}",
        f"- orthogonal warning: {a['orthogonal_warning']}",
        f"- harmless projection condition: {a['harmless_projection_condition']}",
        "",
        "## Closure Requirements",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
    lines.extend(["", "## Blocked Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["blocked_shortcuts"])
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
