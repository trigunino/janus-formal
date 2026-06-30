from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_lorentz_polar_projection_regular_branch.md")
JSON_PATH = Path("outputs/reports/p0_lorentz_polar_projection_regular_branch.json")


def build_payload() -> dict:
    regularity_conditions = [
        "L_geom is invertible on the evaluated patch",
        "eta-adjoint product H=eta^{-1} L_geom^T eta L_geom admits the chosen real regular square-root branch",
        "polar_eta(L_geom)=L_geom H^{-1/2} is smooth on the patch",
        "time orientation and determinant sector are fixed consistently with the target Lorentz branch",
    ]
    singular_branch_failures = [
        "det(L_geom)=0 or rank drop",
        "H has spectrum on a square-root branch cut or defective Jordan structure",
        "the selected root branch changes discontinuously across the patch",
        "polar_eta selects the wrong orthochronous/proper Lorentz component",
        "metric/signature mismatch in the eta-adjoint construction",
    ]
    derivative_open_items = [
        "D_alpha L_Lorentz = D_alpha polar_eta(L_geom) requires the derivative of the eta-polar projection",
        "D_alpha H and D_alpha H^{-1/2} must be handled on the same regular branch",
        "projection derivative must be source-derived before it can close Bianchi residuals",
        "raw spin-connection derivatives of L_geom do not by themselves give D_alpha L_Lorentz",
    ]
    blockers = [
        "zero-divergence PDE blocker remains open: no proof that projected L solves the needed residual equations",
        "K/Q_cross same-L blocker remains open: the same projected L must induce K transport and optical Q_cross",
        "Janus source-derived blocker remains open: polar projection is a construction, not a source equation",
    ]
    return {
        "description": "Broad-pass P0 artifact for the Lorentz polar projection of the raw solder map L_geom.",
        "status": "regular-branch-artifact",
        "definition": "L_Lorentz=polar_eta(L_geom)",
        "regular_branch_only": True,
        "lorentz_admissibility": "admissible by construction where polar_eta is defined on the selected regular branch",
        "source_derived": False,
        "d_lorentz_derivative_closed": False,
        "zero_divergence_pde_closed": False,
        "same_l_for_k_and_qcross": False,
        "prediction_ready": False,
        "regularity_conditions": regularity_conditions,
        "singular_branch_failures": singular_branch_failures,
        "derivative_open_items": derivative_open_items,
        "blockers": blockers,
        "rejection_rules": [
            "do not treat polar_eta regularity as closure; it is not a Janus source derivation",
            "do not use L_Lorentz for prediction until D L, zero-divergence PDE, and K/Q_cross same-L blockers close",
            "do not extend the branch through singular or discontinuous polar data",
        ],
        "verdict": (
            "The polar-projected map is Lorentz-admissible by construction only on "
            "regular branches. It is not source-derived, does not close D L, and "
            "cannot support predictions until the projection derivative, "
            "zero-divergence PDE, and K/Q_cross same-L blockers are resolved."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Lorentz Polar Projection Regular Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Regular branch only: {payload['regular_branch_only']}",
        f"Lorentz admissibility: {payload['lorentz_admissibility']}",
        f"Source-derived: {payload['source_derived']}",
        f"D L_Lorentz derivative closed: {payload['d_lorentz_derivative_closed']}",
        f"Zero-divergence PDE closed: {payload['zero_divergence_pde_closed']}",
        f"Same L for K and Q_cross: {payload['same_l_for_k_and_qcross']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Regularity Conditions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["regularity_conditions"])
    lines.extend(["", "## Singular/Branch Failures", ""])
    lines.extend(f"- {item}" for item in payload["singular_branch_failures"])
    lines.extend(["", "## D L Open Items", ""])
    lines.extend(f"- {item}" for item in payload["derivative_open_items"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
