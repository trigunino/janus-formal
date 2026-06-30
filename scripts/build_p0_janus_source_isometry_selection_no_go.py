from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_source_isometry_selection_no_go.md")
JSON_PATH = Path("outputs/reports/p0_janus_source_isometry_selection_no_go.json")


def weakfield_identity_isometry_residuals() -> dict[str, str]:
    phi_p, phi_m, psi_p, psi_m = sp.symbols("Phi_plus Phi_minus Psi_plus Psi_minus")
    return {
        "time": sp.sstr(sp.simplify(2 * (phi_p - phi_m))),
        "space": sp.sstr(sp.simplify(-2 * (psi_p - psi_m))),
    }


def weakfield_relative_poisson_residual() -> str:
    lap_rel, chi, rho_m_to_p, rho_p_to_m, source_plus, source_minus = sp.symbols(
        "Lap_rel chi rho_m_to_p rho_p_to_m S_plus S_minus"
    )
    relative = sp.symbols("Psi_rel")
    residual = sp.simplify(
        2 * lap_rel
        - 2 * chi * (rho_m_to_p - rho_p_to_m) * relative
        - chi * (source_plus + source_minus)
    )
    return sp.sstr(residual)


def build_payload() -> dict:
    isometry_residuals = weakfield_identity_isometry_residuals()
    source_relative = weakfield_relative_poisson_residual()
    audit_rows = [
        {
            "row": "identity_metric_pullback",
            "janus_input": "weak-field Newtonian gauge metrics",
            "imposes": "Phi_plus=Phi_minus and Psi_plus=Psi_minus on identity-map branch",
            "source_derives_isometry": False,
        },
        {
            "row": "linear_diffeomorphism_metric_pullback",
            "janus_input": "h_plus-h_minus = Lie_xi eta",
            "imposes": "relative metric must be pure gauge; curvature/tidal invariants must match",
            "source_derives_isometry": False,
        },
        {
            "row": "poisson_source_rows",
            "janus_input": "coupled Poisson rows for Psi_plus and Psi_minus",
            "imposes": f"relative residual `{source_relative}`",
            "source_derives_isometry": False,
        },
        {
            "row": "curvature_matching",
            "janus_input": "Riemann[g_plus]=phi^*Riemann[g_minus]",
            "imposes": "sector curvature invariants equal pointwise",
            "source_derives_isometry": False,
        },
        {
            "row": "special_equal_branch",
            "janus_input": "equal potentials, matched sources, boundary mode fixed",
            "imposes": "metric-compatible phi may exist",
            "source_derives_isometry": True,
        },
    ]
    no_go_reasons = [
        "Janus source rows determine potentials from sector sources; they do not equate the two metrics.",
        "Metric pullback isometry would remove relative curvature degrees needed by generic two-metric Janus branches.",
        "The B4vol determinant row fixes a source weight, not the full Jacobian/isometry PDE.",
        "Weak-field equality Phi_plus=Phi_minus and Psi_plus=Psi_minus is a special branch, not a published general selector.",
    ]
    allowed_routes = [
        "keep L_solder as a special metric-compatible diagnostic branch",
        "derive a weaker connection/dust-congruence selector instead of full metric isometry",
        "derive a sourced GL/strain or polar-L law with stability proof if relative metric strain is physical",
    ]
    return {
        "description": "Audit whether Janus source equations select the metric-pullback isometry needed by pure L_solder.",
        "status": "janus-source-does-not-select-generic-metric-isometry",
        "identity_isometry_residuals": isometry_residuals,
        "weakfield_relative_poisson_residual": source_relative,
        "audit_rows": audit_rows,
        "no_go_reasons": no_go_reasons,
        "allowed_routes": allowed_routes,
        "identity_branch_requires_equal_phi": True,
        "identity_branch_requires_equal_psi": True,
        "curvature_matching_required": True,
        "b4vol_selects_measure_not_isometry": True,
        "janus_source_selects_generic_metric_isometry": False,
        "special_equal_branch_conditionally_allowed": True,
        "pure_l_solder_generic_route_rejected": True,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The Janus source rows do not select a generic metric-pullback isometry. "
            "Pure L_solder is therefore valid only as a special equal-curvature/equal-potential "
            "branch. The general non-rustine route must be weaker than full metric isometry."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Source Isometry Selection No-Go",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Identity branch requires equal Phi: {payload['identity_branch_requires_equal_phi']}",
        f"Identity branch requires equal Psi: {payload['identity_branch_requires_equal_psi']}",
        f"Curvature matching required: {payload['curvature_matching_required']}",
        f"B4vol selects measure not isometry: {payload['b4vol_selects_measure_not_isometry']}",
        f"Janus source selects generic metric isometry: {payload['janus_source_selects_generic_metric_isometry']}",
        f"Special equal branch conditionally allowed: {payload['special_equal_branch_conditionally_allowed']}",
        f"Pure L_solder generic route rejected: {payload['pure_l_solder_generic_route_rejected']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identity Residuals",
        "",
    ]
    for name, value in payload["identity_isometry_residuals"].items():
        lines.append(f"- {name}: `{value}`")
    lines.extend(
        [
            "",
            f"Weak-field relative Poisson residual: `{payload['weakfield_relative_poisson_residual']}`",
            "",
            "## Audit Rows",
            "",
            "| row | Janus input | imposes | source derives isometry |",
            "|---|---|---|---:|",
        ]
    )
    for row in payload["audit_rows"]:
        lines.append(
            f"| {row['row']} | `{row['janus_input']}` | {row['imposes']} | "
            f"{row['source_derives_isometry']} |"
        )
    lines.extend(["", "## No-Go Reasons", ""])
    lines.extend(f"- {item}" for item in payload["no_go_reasons"])
    lines.extend(["", "## Allowed Routes", ""])
    lines.extend(f"- {item}" for item in payload["allowed_routes"])
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
