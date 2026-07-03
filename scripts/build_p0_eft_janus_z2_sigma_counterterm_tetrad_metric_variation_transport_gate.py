from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate.json")


def build_payload() -> dict:
    declared = {
        "tetrad_variation_transport_gate_imported": True,
        "tetrad_metric_identity_bibliography_checked": True,
        "induced_metric_formula_declared": True,
        "coframe_variation_basis_declared": True,
        "z2_orientation_no_effect_on_metric_declared": True,
        "no_metric_only_shortcut": True,
        "delta_h_formula_declared": True,
    }
    closure = {
        "delta_h_in_allowed_basis": True,
        "induced_metric_variation_transport_ready": True,
    }
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-metric-variation-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "tetrad/coframe metric identity g = eta_IJ e^I e^J",
            "induced boundary metric h_ab = eta_IJ e_a^I e_b^J",
            "first-order tetrad variation of the induced metric",
        ],
        "source_links": [
            "https://arxiv.org/abs/gr-qc/9209012",
            "https://math.mit.edu/~hrm/palestine/lee-smooth-manifolds.pdf",
        ],
        "bibliography_result": (
            "The induced metric variation follows algebraically from the tetrad identity. "
            "This closes only delta e -> delta h_ab; delta K and torsion-pullback "
            "transports remain separate open obligations."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "induced_metric": "h_ab = eta_IJ e_a^I e_b^J",
            "metric_variation": "delta h_ab = eta_IJ(delta e_a^I e_b^J + e_a^I delta e_b^J)",
            "z2_orientation": "orientation sign affects normal/extrinsic data, not h_ab algebraically",
        },
        "tetrad_metric_variation_ledger_declared": all(declared.values()),
        "tetrad_metric_variation_transport_ready": all(declared.values()) and all(closure.values()),
        "closed": [
            "induced_metric_variation_transport_ready",
            "delta_h_in_allowed_basis",
        ],
        "still_open": [
            "extrinsic_curvature_variation_transport_ready",
            "torsion_pullback_variation_transport_ready",
            "full_tetrad_variation_transport_ready",
        ],
        "next_required": [
            "derive_delta_e_to_delta_K_transport_from_embedding_extrinsic_curvature_gate",
            "derive_delta_e_to_torsion_pullback_variation_transport",
            "feed_induced_metric_variation_transport_ready_to_tetrad_variation_transport_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Metric Variation Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['tetrad_metric_variation_ledger_declared']}`",
        f"Transport ready: `{payload['tetrad_metric_variation_transport_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
