from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_derived_closure_checklist.md")
JSON_PATH = Path("outputs/reports/p0_source_derived_closure_checklist.json")


SOURCE_TRACEABILITY = "docs/source_traceability.md"


P0_SOURCE_DERIVATION_ITEMS = [
    {
        "item": "L transport maps",
        "symbols": ["L_minus_to_plus", "L_plus_to_minus"],
        "must_be_derived_from": [
            "Janus coupled field equations",
            "published bimetric/geodesic source anchors",
        ],
        "must_not_be_imposed_as": [
            "raw geometric tetrad solder map",
            "lensing-tuned projection map",
        ],
        "source_traceability_hooks": [
            "Coupled field equations",
            "Two geodesic families",
            "build_qcross_geometric_tetrad_map_derivation.py",
        ],
        "status": "open",
    },
    {
        "item": "D L and connection-force cancellation",
        "symbols": ["D L", "C^mu_{nu a}", "R_plus^mu", "R_minus^mu"],
        "must_be_derived_from": [
            "cross-sector covariant transport",
            "connection-difference terms in the Bianchi residuals",
        ],
        "must_not_be_imposed_as": [
            "set D L = 0 by convention",
            "drop connection-force terms",
        ],
        "source_traceability_hooks": [
            "build_bianchi_l_derivative_obstruction.py",
            "build_bianchi_connection_force_cancellation_target.py",
        ],
        "status": "open",
    },
    {
        "item": "Transported continuity",
        "symbols": [
            "D_minus(rho_minus u_minus_to_plus)",
            "D_plus(rho_plus u_plus_to_minus)",
        ],
        "must_be_derived_from": [
            "same-sector conservation plus Janus transport map",
            "published continuity/field-equation constraints",
        ],
        "must_not_be_imposed_as": [
            "copied dust continuity in the other metric",
            "scalar density rescaling only",
        ],
        "source_traceability_hooks": [
            "build_bianchi_transported_continuity_target.py",
            "build_bianchi_conditional_closure_theorem.py",
        ],
        "status": "open",
    },
    {
        "item": "Transported force equation",
        "symbols": ["u D u + C u u", "u D u - C u u"],
        "must_be_derived_from": [
            "positive and negative geodesic equations",
            "cross-sector connection-force transport",
        ],
        "must_not_be_imposed_as": [
            "ordinary same-sector geodesic closure only",
            "phenomenological force cancellation",
        ],
        "source_traceability_hooks": [
            "Two geodesic families",
            "build_bianchi_transported_geodesic_force_target.py",
            "build_bianchi_connection_force_cancellation_target.py",
        ],
        "status": "open",
    },
    {
        "item": "K tensor compatibility",
        "symbols": ["K_plus", "K_minus", "M_minus_to_plus", "M_plus_to_minus"],
        "must_be_derived_from": [
            "the same L maps used by Q_cross",
            "Bianchi mixed-stress residual equations",
        ],
        "must_not_be_imposed_as": [
            "naive copied stress tensor",
            "independent Q_cross/Q_det scalar factor",
        ],
        "source_traceability_hooks": [
            "build_bianchi_mixed_transport_map_target.py",
            "build_lensing_qdet_qcross_derivation_map.py",
            "build_p0_l_k_qcross_consistency_target.py",
            "build_p0_janus_transport_residual_derivation.py",
        ],
        "status": "open",
    },
    {
        "item": "Matter extension",
        "symbols": ["p", "h^mu_nu", "Pi^mu_nu", "w_cross"],
        "must_be_derived_from": [
            "perfect-fluid and anisotropic-stress tensor transport",
            "equation-of-state transport from Janus source equations",
        ],
        "must_not_be_imposed_as": [
            "dust-only closure reused for pressure",
            "absorbing tensor pressure/Pi into scalar Q_cross or Q_det",
        ],
        "source_traceability_hooks": [
            "build_bianchi_flrw_perfect_fluid_transport_branch.py",
            "build_bianchi_anisotropic_stress_transport_target.py",
            "build_bianchi_tensor_matter_extension_target.py",
        ],
        "status": "open",
    },
    {
        "item": "Metric potential / Weyl chain",
        "symbols": ["Phi_lens_plus", "delta G_plus[h_plus]", "gamma1", "gamma2"],
        "must_be_derived_from": [
            "Janus linearized field equation",
            "gauge/slip/source-identity closure for the simulated source class",
        ],
        "must_not_be_imposed_as": [
            "PM Poisson potential promoted directly to metric potential",
            "survey-fitted shear or sigma8/S8 normalization",
        ],
        "source_traceability_hooks": [
            "weak_field_weyl_screen_tidal_components_2d",
            "positive_photon_weak_field_weyl_components_2d",
            "build_p0_stueckelberg_metric_potential_promotion_gate.py",
        ],
        "status": "open",
    },
]


def build_payload() -> dict:
    return {
        "description": (
            "P0 checklist for assumptions that must be derived from Janus field "
            "equations and published source anchors, not imposed as closures."
        ),
        "source_traceability_file": SOURCE_TRACEABILITY,
        "all_items_source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "items": P0_SOURCE_DERIVATION_ITEMS,
        "forbidden_shortcuts": [
            "treat scalar Q_cross as a tensor transport map",
            "treat scalar Q_det as pressure or anisotropic-stress transport",
            "use raw scale/determinant ratios as optical amplitudes",
            "declare Bianchi closure from dust-only assumptions",
        ],
        "verdict": (
            "No P0 assumption is allowed to become a prediction input until its "
            "source-traceability hook is upgraded from target/audit to source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Derived Closure Checklist",
        "",
        payload["description"],
        "",
        f"Source traceability: `{payload['source_traceability_file']}`",
        f"All items source-derived: {payload['all_items_source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| item | symbols | must be derived from | must not be imposed as | hooks | status |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["items"]:
        symbols = ", ".join(f"`{symbol}`" for symbol in row["symbols"])
        derived = "; ".join(row["must_be_derived_from"])
        forbidden = "; ".join(row["must_not_be_imposed_as"])
        hooks = ", ".join(f"`{hook}`" for hook in row["source_traceability_hooks"])
        lines.append(
            f"| {row['item']} | {symbols} | {derived} | {forbidden} | {hooks} | {row['status']} |"
        )
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
