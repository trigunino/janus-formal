from __future__ import annotations

import json
from pathlib import Path


RATIO_PATH = Path("outputs/active_z2_sigma/rsigma_over_ell_collar_solution.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_optimal_reference_embedding_scale_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_optimal_reference_embedding_scale_gate.json"
)


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(*, ratio_path: Path = RATIO_PATH) -> dict:
    ratio = _read_json(ratio_path) or {}
    closure = {
        "isometric_reference_embedding_prescription_declared": True,
        "reference_time_vector_prescription_declared": True,
        "reference_energy_extremization_prescription_declared": True,
        "reference_zero_energy_condition_declared": True,
        "k_ref_fixed_from_boundary_metric_if_RSigma_known": True,
        "R_Sigma_over_ell_collar_ratio_available": bool(ratio.get("ratio_solution_ready")),
        "absolute_R_Sigma_fixed_by_reference_prescription": False,
        "absolute_ell_collar_fixed_by_reference_prescription": False,
    }
    return {
        "status": "janus-z2-sigma-optimal-reference-embedding-scale-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_route": "Chen_Nester_optimal_reference_plus_BrownYork_FRW",
        "result": (
            "The optimal/isometric reference fixes the boundary subtraction and "
            "k_ref once the intrinsic boundary metric is fixed. It does not by "
            "itself choose the absolute throat scale R_Sigma."
        ),
        "closure": closure,
        "reference_prescription_ready": all(
            closure[key]
            for key in [
                "isometric_reference_embedding_prescription_declared",
                "reference_time_vector_prescription_declared",
                "reference_energy_extremization_prescription_declared",
                "reference_zero_energy_condition_declared",
                "k_ref_fixed_from_boundary_metric_if_RSigma_known",
            ]
        ),
        "absolute_scale_fixed": False,
        "allowed_conclusion": "reference_fixes_zero_and_k_ref_not_RSigma",
        "forbidden_conclusion": "reference_extremization_alone_derives_absolute_RSigma",
        "next_required": [
            "derive_absolute_R_Sigma_from_global_Janus_tunnel_or_boundary_metric",
            "or_supply_active_boundary_metric_with_dimensionful_R_Sigma",
            "then_apply_optimal_reference_embedding_to_compute_E_BY",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Optimal Reference Embedding Scale Gate",
        "",
        payload["result"],
        "",
        f"Reference prescription ready: `{payload['reference_prescription_ready']}`",
        f"Absolute scale fixed: `{payload['absolute_scale_fixed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
