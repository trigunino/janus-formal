from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_lgeom_lorentz_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_lgeom_lorentz_no_go_gate.json")


def weakfield_lgeom() -> sp.Matrix:
    delta_phi, delta_psi = sp.symbols("Delta_Phi Delta_Psi")
    return sp.diag(1 - delta_phi, 1 + delta_psi, 1 + delta_psi, 1 + delta_psi)


def linear_lorentz_residual() -> sp.Matrix:
    delta_phi, delta_psi = sp.symbols("Delta_Phi Delta_Psi")
    eta = sp.diag(-1, 1, 1, 1)
    residual = weakfield_lgeom().T * eta * weakfield_lgeom() - eta
    return residual.applyfunc(
        lambda expr: sp.expand(expr).subs({delta_phi**2: 0, delta_psi**2: 0, delta_phi * delta_psi: 0})
    )


def build_payload() -> dict:
    residual = linear_lorentz_residual()
    return {
        "description": (
            "Local weak-field no-go gate for using the raw geometric solder map L_geom "
            "as the admissible same-L map for K transport and Q_cross."
        ),
        "status": "weakfield-lgeom-lorentz-no-go-open",
        "depends_on": [
            "qcross_geometric_tetrad_map_derivation",
            "p0_l_k_qcross_consistency_target",
            "p0_janus_weakfield_metric_tetrad_bridge",
        ],
        "weakfield_metric_branch": "ds_s^2=-(1+2 Phi_s)dt^2+(1-2 Psi_s)delta_ij dx^i dx^j",
        "lgeom_linear": "diag(1-Delta_Phi, 1+Delta_Psi, 1+Delta_Psi, 1+Delta_Psi)",
        "lorentz_residual_linear": [[sp.sstr(item) for item in row] for row in residual.tolist()],
        "lorentz_condition": "Delta_Phi=0 and Delta_Psi=0 at linear order",
        "dust_slip_consequence": "Phi_s=Psi_s does not make L_geom Lorentz unless the relative potential also vanishes",
        "no_go_rows": [
            {
                "case": "generic weak-field relative potentials",
                "lgeom_admissible": False,
                "reason": "L_geom^T eta L_geom - eta has Delta_Phi/Delta_Psi diagonal residuals",
            },
            {
                "case": "dust/slip but nonzero relative potential",
                "lgeom_admissible": False,
                "reason": "Phi=Psi per sector leaves Delta_Phi=Delta_Psi nonzero",
            },
            {
                "case": "identical local potentials",
                "lgeom_admissible": True,
                "reason": "linear Lorentz residual vanishes, reducing to the equal-frame branch",
            },
        ],
        "allowed_next_routes": [
            "derive a Lorentz map L from a source-selected tetrad gauge/connection law",
            "use a Lorentz polar/boost projection only if its source rule and K residuals are proved",
            "keep FLRW comoving L=I as a special equal-frame branch",
        ],
        "forbidden_shortcuts": [
            "use L_geom for Q_cross while a different map transports K_plus/K_minus",
            "treat the L_geom diagonal stretch as an optical scalar amplitude",
            "absorb the Lorentz residual into Q_det or Q_cross",
        ],
        "lgeom_lorentz_condition_derived": True,
        "lgeom_generic_branch_rejected": True,
        "flrw_equal_frame_branch_allowed": True,
        "source_selected_perturbed_l_found": False,
        "same_l_global_perturbed_branch_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The raw weak-field L_geom cannot be the global perturbed same-L map except "
            "in the equal-potential branch. A real perturbed L must come from a Lorentz "
            "source/tetrad transport law and then close K and Q_cross together."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Lgeom Lorentz No-Go Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weak-field metric branch: `{payload['weakfield_metric_branch']}`",
        f"L_geom linear: `{payload['lgeom_linear']}`",
        f"Lorentz condition: `{payload['lorentz_condition']}`",
        f"Dust/slip consequence: {payload['dust_slip_consequence']}",
        f"L_geom Lorentz condition derived: {payload['lgeom_lorentz_condition_derived']}",
        f"L_geom generic branch rejected: {payload['lgeom_generic_branch_rejected']}",
        f"Source-selected perturbed L found: {payload['source_selected_perturbed_l_found']}",
        f"Same-L global perturbed branch selected: {payload['same_l_global_perturbed_branch_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## No-Go Rows",
        "",
        "| case | L_geom admissible | reason |",
        "|---|---|---|",
    ]
    for row in payload["no_go_rows"]:
        lines.append(f"| {row['case']} | {row['lgeom_admissible']} | {row['reason']} |")
    lines.extend(["", "## Allowed Next Routes", ""])
    lines.extend(f"- {item}" for item in payload["allowed_next_routes"])
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
