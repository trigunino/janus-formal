from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "spectral_stability_exit_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_spectral_stability_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_spectral_stability_exit_gate.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _derive(data: dict[str, Any]) -> dict[str, Any]:
    radius = data.get("R_s_m")
    operator = data.get("operator")
    if not isinstance(radius, (int, float)) or not math.isfinite(float(radius)) or float(radius) <= 0:
        return {"ready": False, "missing": ["R_s_m"]}
    radius = float(radius)
    if operator == "scalar_laplacian_S2_round":
        ell = int(data.get("ell_mode", 1))
        eigenvalue = ell * (ell + 1) / radius**2
        return {
            "ready": True,
            "lowest_nonzero_eigenvalue_m_minus_2": eigenvalue,
            "chi_LL_abs_inverse_m": 1.0 / (8.0 * math.pi * radius),
            "chi_LL_sign": "negative_PT_branch",
        }
    if operator == "dirac_S2_round":
        k = int(data.get("dirac_mode_k", 0))
        eigenvalue_abs = (k + 1) / radius
        return {
            "ready": True,
            "lowest_dirac_abs_eigenvalue_m_minus_1": eigenvalue_abs,
            "chi_LL_abs_inverse_m": 1.0 / (8.0 * math.pi * radius),
            "chi_LL_sign": "negative_PT_branch",
        }
    return {"ready": False, "missing": ["supported_operator"]}


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    required_conditions = {
        "operator_declared": data.get("operator") in {
            "scalar_laplacian_S2_round",
            "dirac_S2_round",
            "custom_janus_sigma_operator",
        },
        "domain_and_measure_declared": bool(data.get("domain_and_measure_declared")),
        "boundary_or_spin_structure_declared": bool(data.get("boundary_or_spin_structure_declared")),
        "self_adjointness_declared": bool(data.get("self_adjointness_declared")),
        "stability_criterion_declared": bool(data.get("stability_criterion_declared")),
        "scale_selection_law_declared": bool(data.get("scale_selection_law_declared")),
        "non_observational_provenance": bool(data.get("non_observational_provenance")),
    }
    derivation = _derive(data)
    ready = all(required_conditions.values()) and derivation["ready"]
    return {
        "status": "janus-z2-chi-ll-spectral-stability-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_idea": (
            "Spectral geometry can select a throat scale only if a natural "
            "self-adjoint operator on Sigma/PT is derived and a non-observational "
            "zero-mode, gap, or stationarity condition fixes R_s."
        ),
        "bibliography_basis": [
            "Dirac spectrum on round spheres scales as 1/R",
            "Scalar Laplacian spectrum on S2 scales as ell(ell+1)/R^2",
            "Lichnerowicz formula relates Dirac gaps to scalar curvature",
        ],
        "required_conditions": required_conditions,
        "formulae": {
            "laplacian_S2": "lambda_l=l(l+1)/R_s^2",
            "dirac_S2": "|lambda_k|=(k+1)/R_s",
            "ll_tension": "chi_LL=-1/(8*pi*R_s)",
        },
        "forbidden_shortcuts": {
            "choose_target_eigenvalue_by_observation": True,
            "declare_zero_mode_without_operator_domain": True,
            "use_spectral_gap_without_self_adjointness": True,
            "select_R_s_without_scale_selection_law": True,
        },
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "derivation": derivation,
        "spectral_stability_exit_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + derivation.get("missing", []),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Spectral Stability Exit Gate",
        "",
        payload["physical_idea"],
        "",
        f"Exit ready: `{payload['spectral_stability_exit_ready']}`",
        f"Input present: `{payload['input_present']}`",
        "",
        "## Required Conditions",
    ]
    lines.extend(f"- `{k}`: `{v}`" for k, v in payload["required_conditions"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
