from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "llbrane_minimal_gauge_action_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_minimal_gauge_action_reducer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_minimal_gauge_action_reducer_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_text(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive(payload: dict[str, Any], key: str, errors: list[str]) -> float:
    value = payload.get(key)
    if not isinstance(value, (int, float)) or not math.isfinite(float(value)):
        errors.append(f"{key}_must_be_finite")
        return 0.0
    value_f = float(value)
    if value_f <= 0.0:
        errors.append(f"{key}_must_be_positive")
    return value_f


def _validate(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if payload.get("a0_matching_value") != 0.125:
        errors.append("a0_matching_value_must_be_1_over_8")
    if _bad_text(payload.get("action_provenance")):
        errors.append("action_provenance_missing_or_forbidden")
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")

    family = payload.get("L_F2_family")
    if family == "monomial_lambda_F2_power_p":
        _positive(payload, "lambda_F2", errors)
        p = _positive(payload, "power_p", errors)
        if p == 0.0:
            errors.append("power_p_must_be_nonzero")
    elif family == "sqrt_F2_unit_normalized":
        pass
    else:
        errors.append("L_F2_family_not_supported")
    return errors


def _compute(payload: dict[str, Any]) -> dict[str, Any]:
    family = payload["L_F2_family"]
    a0 = 0.125
    if family == "sqrt_F2_unit_normalized":
        # L=sqrt(F2) gives F2*dL/dF2 = sqrt(F2)/2 = 1/8.
        f2_aux = 1.0 / 16.0
        return {
            "F2_0_auxiliary_units": f2_aux,
            "F2_0_m_minus_4": None,
            "dimensionful_value_ready": False,
            "formula": "L=sqrt(F2): F2_0_aux=1/16",
        }
    lam = float(payload["lambda_F2"])
    p = float(payload["power_p"])
    # L=lambda*F2^p gives F2*dL/dF2 = lambda*p*F2^p = 1/8.
    f2 = (a0 / (lam * p)) ** (1.0 / p)
    return {
        "F2_0_auxiliary_units": f2,
        "F2_0_m_minus_4": f2 if payload.get("F2_units") == "m_minus_4" else None,
        "dimensionful_value_ready": payload.get("F2_units") == "m_minus_4",
        "formula": "L=lambda*F2^p: F2_0=(1/(8*lambda*p))^(1/p)",
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
) -> dict[str, Any]:
    state = _read(input_path)
    errors = [] if state is None else _validate(state)
    ready = state is not None and not errors
    computed = _compute(state) if ready else None
    candidate_families = {
        "sqrt_F2_unit_normalized": {
            "status": "dimensionless_auxiliary_closure_only",
            "F2_0_auxiliary_units": "1/16",
            "blocker": "does_not_supply_m_minus_4_without_area_or_length_scale",
        },
        "monomial_lambda_F2_power_p": {
            "status": "closes_if_lambda_and_units_are_active_derived",
            "F2_0": "(1/(8*lambda*p))^(1/p)",
            "blocker": "lambda_F2_is_a_new_coupling_unless_derived",
        },
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-minimal-gauge-action-reducer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "input_exists": state is not None,
        "candidate_families": candidate_families,
        "matching_condition": "F2*dL/dF2 = a0 = 1/8",
        "validation_errors": errors,
        "computed": computed,
        "minimal_action_reduces_F2_0": ready,
        "dimensionful_F2_0_ready": bool(computed and computed["dimensionful_value_ready"]),
        "chi_LL_ready_downstream": bool(computed and computed["dimensionful_value_ready"]),
        "gate_passed": bool(computed and computed["dimensionful_value_ready"]),
        "next_required": []
        if computed and computed["dimensionful_value_ready"]
        else [
            "derive_or_adopt_L_F2_family_with_clean_provenance",
            "derive_dimensionful_lambda_or_area_scale_if_needed",
            "feed_F2_0_m_minus_4_to_superselection_flux_reducer",
        ],
        "interpretation": (
            "The LL matching condition can reduce F2_0 once L(F2) is specified. "
            "A scale-free sqrt(F2) action gives only an auxiliary-unit value. "
            "A dimensionful monomial can feed chi_LL only if its coupling is "
            "active-derived rather than fitted."
        ),
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Minimal Gauge Action Reducer Gate",
        "",
        payload["interpretation"],
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Dimensionful F2_0 ready: `{payload['dimensionful_F2_0_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
