from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_source_tetrad_requirements.md")
JSON_PATH = Path("outputs/reports/p0_janus_source_tetrad_requirements.json")


def build_payload() -> dict:
    starting_equations = [
        {
            "item": "positive-sector metric/source equation",
            "working_form": (
                "G_plus[g_plus] = kappa(source_plus - cross_source_minus_to_plus)"
            ),
            "requirement": "derive h_plus or delta g_plus from the coupled Janus source equation",
        },
        {
            "item": "negative-sector metric/source equation",
            "working_form": (
                "G_minus[g_minus] = kappa(source_minus - cross_source_plus_to_minus)"
            ),
            "requirement": "derive h_minus or delta g_minus from the mirror coupled source equation",
        },
        {
            "item": "Bianchi-compatible source transport",
            "working_form": "nabla_plus RHS_plus = 0 and nabla_minus RHS_minus = 0",
            "requirement": "keep the metric, tetrad, connection, and cross-map layers source-derived",
        },
    ]
    requirements = [
        {
            "object": "g_plus / g_minus",
            "symbol": "g_plus = g_plus_background + h_plus[source], g_minus = g_minus_background + h_minus[source]",
            "must_be_source_derived": "metric perturbations solved from Janus coupled sources",
            "not_allowed": "fit metric potentials or import PM Poisson potentials as final metric data",
            "status": "open",
        },
        {
            "object": "e_plus / e_minus",
            "symbol": "g_{plus/minus mu nu} = eta_AB e_{plus/minus}^A_mu e_{plus/minus}^B_nu",
            "must_be_source_derived": "tetrads built from the source-derived metrics with declared Lorentz gauge",
            "not_allowed": "choose a convenient optical tetrad before the metric derivation is closed",
            "status": "open",
        },
        {
            "object": "omega_plus / omega_minus",
            "symbol": "omega_{plus/minus} from de + omega wedge e = 0",
            "must_be_source_derived": "spin connections computed from e_plus/e_minus and the sector Levi-Civita connections",
            "not_allowed": "set omega rows by a transport ansatz or by Omega_u u = 0 without a source law",
            "status": "open",
        },
        {
            "object": "F_relative",
            "symbol": "F_relative = curvature of A_relative, A_relative = omega_plus - L omega_minus L^-1 - dL L^-1",
            "must_be_source_derived": "relative curvature assembled from source-derived omega_plus, omega_minus, and L",
            "not_allowed": "inject weak-field curvature rows as the full Janus relative curvature",
            "status": "open",
        },
        {
            "object": "L",
            "symbol": "L_minus_to_plus and L_plus_to_minus",
            "must_be_source_derived": "cross frame map selected by the coupled metric/source system and Bianchi residuals",
            "not_allowed": "use raw tetrad soldering, L=I, D L=0, or lensing-tuned maps as closure",
            "status": "open",
        },
    ]
    forbidden_shortcuts = [
        "no observational fit for g_plus, g_minus, e_plus, e_minus, omega_plus, omega_minus, F_relative, or L",
        "no scalar absorption of tetrad, spin-connection, curvature, or cross-map terms into Q_cross/Q_det",
        "do not promote the weak-field tetrad branch to a full Janus source derivation",
        "do not set L, D L, or omega rows by convention before source transport is derived",
    ]
    return {
        "description": (
            "Bounded P0 requirements for a Janus source-derived tetrad layer starting "
            "from the coupled metric/source equations."
        ),
        "status": "source-derived-tetrad-requirements-open",
        "scope": "requirements artifact only; no new source law and no prediction",
        "starting_equations": starting_equations,
        "requirements": requirements,
        "weak_field_branch": {
            "name": "Newtonian-gauge weak-field tetrad",
            "form": "e0=(1+Phi)dt, ei=(1-Psi)dxi, linear order",
            "role": "provisional branch for audits and symbolic row targets only",
            "full_janus_derivation": False,
        },
        "forbidden_shortcuts": forbidden_shortcuts,
        "source_derived_metric_perturbations_required": True,
        "source_derived_tetrads_required": True,
        "source_derived_spin_connections_required": True,
        "source_derived_relative_curvature_required": True,
        "source_derived_cross_map_required": True,
        "weak_field_tetrad_only_provisional": True,
        "full_janus_tetrad_source_derivation_open": True,
        "uses_observational_fit": False,
        "scalar_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The weak-field tetrad remains a provisional branch. A full Janus tetrad/source "
            "derivation must still derive g_plus/g_minus, e_plus/e_minus, omega_plus/"
            "omega_minus, F_relative, and L from the coupled source equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Source-Derived Tetrad Requirements",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"Weak-field tetrad only provisional: {payload['weak_field_tetrad_only_provisional']}",
        f"Full Janus tetrad/source derivation open: {payload['full_janus_tetrad_source_derivation_open']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Starting Equations",
        "",
        "| item | working form | requirement |",
        "|---|---|---|",
    ]
    for row in payload["starting_equations"]:
        lines.append(
            f"| {row['item']} | `{row['working_form']}` | {row['requirement']} |"
        )
    lines.extend(
        [
            "",
            "## Source-Derived Requirements",
            "",
            "| object | symbol | must be source-derived | not allowed | status |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["requirements"]:
        lines.append(
            "| {object} | `{symbol}` | {must_be_source_derived} | {not_allowed} | {status} |".format(
                **row
            )
        )
    branch = payload["weak_field_branch"]
    lines.extend(
        [
            "",
            "## Weak-Field Branch",
            "",
            f"- Name: {branch['name']}",
            f"- Form: `{branch['form']}`",
            f"- Role: {branch['role']}",
            f"- Full Janus derivation: {branch['full_janus_derivation']}",
            "",
            "## Forbidden Shortcuts",
            "",
        ]
    )
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
