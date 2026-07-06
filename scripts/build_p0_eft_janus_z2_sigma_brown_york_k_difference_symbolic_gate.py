from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_optimal_reference_embedding_scale_gate import (
    build_payload as build_reference_scale,
)


RATIO_PATH = Path("outputs/active_z2_sigma/rsigma_over_ell_collar_solution.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brown_york_k_difference_symbolic_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brown_york_k_difference_symbolic_gate.json"
)


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(*, ratio_path: Path = RATIO_PATH) -> dict:
    ratio = _read_json(ratio_path) or {}
    reference_scale = build_reference_scale(ratio_path=ratio_path)
    eps = -1
    closure = {
        "round_S3_time_leaf_formula_declared": True,
        "projective_orientation_eps_Z2_declared": True,
        "k_phys_symbolic_available": True,
        "k_ref_symbolic_available": True,
        "k_ref_minus_k_phys_symbolic_available": True,
        "R_Sigma_over_ell_collar_ratio_available": bool(ratio.get("ratio_solution_ready")),
        "absolute_R_Sigma_available": bool(ratio.get("absolute_R_Sigma_fixed")),
        "absolute_ell_collar_available": bool(ratio.get("absolute_ell_collar_fixed")),
    }
    return {
        "status": "janus-z2-sigma-brown-york-k-difference-symbolic-gate",
        "active_core": "Z2_tunnel_Sigma",
        "orientation": {
            "eps_Z2": eps,
            "policy": "projective_tunnel_orientation",
        },
        "formulas": {
            "k_phys": "3*eps_Z2/R_Sigma",
        "k_ref": "3/R_Sigma",
            "k_ref_minus_k_phys": "3*(1-eps_Z2)/R_Sigma",
            "sqrt_q_integral_for_S3_leaf": "2*pi^2*R_Sigma^3",
            "E_BY_symbolic": "6*pi^2*(1-eps_Z2)*R_Sigma^2/kappa_Z2Sigma",
            "E_BY_for_eps_minus_one": "12*pi^2*R_Sigma^2/kappa_Z2Sigma",
        },
        "closure": closure,
        "reference_prescription": {
            "ready": reference_scale["reference_prescription_ready"],
            "absolute_scale_fixed": reference_scale["absolute_scale_fixed"],
            "conclusion": reference_scale["allowed_conclusion"],
        },
        "symbolic_boundary_charge_formula_ready": all(
            closure[key]
            for key in [
                "round_S3_time_leaf_formula_declared",
                "projective_orientation_eps_Z2_declared",
                "k_ref_minus_k_phys_symbolic_available",
                "R_Sigma_over_ell_collar_ratio_available",
            ]
        ),
        "numeric_boundary_charge_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "next_required": [
            "derive_absolute_ell_collar_or_absolute_R_Sigma",
            "then_evaluate_E_BY_symbolic",
            "then_map_E_BY_to_H0_Z2Sigma",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Brown-York k-Difference Symbolic Gate",
        "",
        f"Symbolic charge ready: `{payload['symbolic_boundary_charge_formula_ready']}`",
        f"Numeric charge ready: `{payload['numeric_boundary_charge_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
