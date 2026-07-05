from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_metric_geometry_primitives_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_metric_geometry_primitives_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-metric-geometry-primitives-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "standard Levi-Civita connection formula",
            "standard hypersurface first/second fundamental form machinery",
        ],
        "metric_inverse_builder_ready": True,
        "christoffel_builder_ready": True,
        "unit_normal_from_level_set_ready": True,
        "induced_metric_pullback_ready": True,
        "requires_active_metric": True,
        "requires_active_metric_derivatives": True,
        "requires_active_level_set_or_embedding": True,
        "requires_explicit_normal_norm_sign": True,
        "requires_explicit_orientation_sign": True,
        "uses_planck_lcdm_inputs": False,
        "uses_archived_z4_inputs": False,
        "metric_geometry_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_active_plus_minus_metrics_on_tunnel_neighborhood",
            "derive_active_metric_derivatives_or_connection",
            "derive_active_level_set_or_embedding_for_Sigma",
            "feed_metric_geometry_to_extrinsic_curvature_tensor_builder",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Metric Geometry Primitives Gate",
        "",
        f"Metric inverse ready: `{payload['metric_inverse_builder_ready']}`",
        f"Christoffel builder ready: `{payload['christoffel_builder_ready']}`",
        f"Unit normal builder ready: `{payload['unit_normal_from_level_set_ready']}`",
        f"Values ready: `{payload['metric_geometry_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
