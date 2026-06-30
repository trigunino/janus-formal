from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_tensor_matter_extension_target.md")
JSON_PATH = Path("outputs/reports/bianchi_tensor_matter_extension_target.json")


def build_payload() -> dict:
    tensor_terms = [
        {
            "term": "pressure_metric_term",
            "expression": "p g^{mu nu}",
            "needs_transport": "metric-sector mapping plus source-derived cross pressure",
        },
        {
            "term": "projector",
            "expression": "h^{mu nu}=g^{mu nu}+u^mu u^nu",
            "needs_transport": "projector transport compatible with the same L/K maps",
        },
        {
            "term": "anisotropic_stress",
            "expression": "Pi^{mu nu}",
            "needs_transport": "symmetric trace-free tensor map and transversality preservation",
        },
        {
            "term": "equation_of_state",
            "expression": "p=w rho, p_cross=w_cross rho_cross",
            "needs_transport": "source-derived w_cross instead of imposed scalar closure",
        },
        {
            "term": "divergence_terms",
            "expression": "D_mu[(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}]",
            "needs_transport": "pressure gradients, projector derivatives, D Pi, and connection-force terms",
        },
    ]
    return {
        "description": (
            "Bounded P0 target for extending the Bianchi transport branch beyond dust."
        ),
        "prediction_ready": False,
        "dust_assumptions_enough": False,
        "dust_limit": {
            "stress": "T^{mu nu}=rho u^mu u^nu",
            "why_insufficient": (
                "Dust closure only transports rho and u. It does not transport pressure, "
                "projectors, equation of state, anisotropic stress, or their divergences."
            ),
        },
        "perfect_fluid_target": {
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}",
            "open_terms": ["pressure_metric_term", "projector", "equation_of_state", "divergence_terms"],
            "closed": False,
        },
        "anisotropic_stress_target": {
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}",
            "open_terms": [
                "pressure_metric_term",
                "projector",
                "anisotropic_stress",
                "equation_of_state",
                "divergence_terms",
            ],
            "closed": False,
        },
        "tensor_terms_needing_transport": tensor_terms,
        "forbidden_shortcuts": [
            "do not absorb pressure into scalar Q_cross",
            "do not absorb pressure into scalar Q_det",
            "do not absorb Pi^{mu nu} into scalar Q_cross",
            "do not absorb Pi^{mu nu} into scalar Q_det",
            "do not reuse dust Bianchi closure as perfect-fluid closure",
            "do not reuse scalar FLRW perfect-fluid closure as anisotropic-stress closure",
        ],
        "required_before_closure": [
            "derive pressure and p_cross from Janus source equations",
            "derive projector transport from the same L_minus_to_plus/L_plus_to_minus maps",
            "derive Pi transport preserving symmetry, trace-free condition, and orthogonality",
            "show divergence cancellation in both R_plus and R_minus",
            "verify compatibility with K_plus/K_minus and optical Q_cross",
        ],
        "verdict": (
            "Dust closure assumptions are not enough for perfect-fluid or anisotropic "
            "stress. The extension needs tensor transport and divergence closure before "
            "any prediction claim."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Tensor Matter Extension Target",
        "",
        payload["description"],
        "",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Dust assumptions enough: {payload['dust_assumptions_enough']}",
        "",
        "## Dust Limit",
        "",
        f"- stress: `{payload['dust_limit']['stress']}`",
        f"- why insufficient: {payload['dust_limit']['why_insufficient']}",
        "",
        "## Tensor Terms Needing Transport",
        "",
        "| term | expression | needs transport |",
        "|---|---|---|",
    ]
    for term in payload["tensor_terms_needing_transport"]:
        lines.append(
            f"| {term['term']} | `{term['expression']}` | {term['needs_transport']} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Required Before Closure", ""])
    lines.extend(f"- {item}" for item in payload["required_before_closure"])
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
