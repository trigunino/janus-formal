from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "llbrane_gauge_action_normalization_inputs.json"
ACTION_OUTPUT_PATH = BASE / "llbrane_minimal_gauge_action_inputs.json"
FLUX_OUTPUT_PATH = BASE / "llbrane_s2_flux_superselection_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_gauge_action_normalization_pipeline.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_gauge_action_normalization_pipeline.json"
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
    if payload.get("L_F2_family") != "monomial_lambda_F2_power_p":
        errors.append("L_F2_family_must_be_monomial_lambda_F2_power_p")
    if payload.get("area_gauge") != "physical_induced_S2_metric":
        errors.append("area_gauge_must_be_physical_induced_S2_metric")
    if payload.get("normalization_proved") is not True:
        errors.append("normalization_must_be_proved")
    if payload.get("SO3_flux_ansatz_proved") is not True:
        errors.append("SO3_flux_ansatz_must_be_proved")
    if payload.get("flux_quantization_proved") is not True:
        errors.append("flux_quantization_must_be_proved")
    if _bad_text(payload.get("normalization_provenance")):
        errors.append("normalization_provenance_missing_or_forbidden")

    n = payload.get("flux_integer_n")
    if not isinstance(n, int):
        errors.append("flux_integer_n_must_be_integer")
    elif n == 0:
        errors.append("flux_integer_n_must_be_nonzero")
    _positive(payload, "q_LL_dimensionless", errors)
    _positive(payload, "lambda_F2", errors)
    _positive(payload, "power_p", errors)
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def _f2(lambda_f2: float, power_p: float) -> float:
    return (0.125 / (lambda_f2 * power_p)) ** (1.0 / power_p)


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    action_output_path: Path = ACTION_OUTPUT_PATH,
    flux_output_path: Path = FLUX_OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    state = _read(input_path)
    errors = [] if state is None else _validate(state)
    ready = state is not None and not errors
    action_payload = None
    flux_payload = None
    f2_value = None

    if ready:
        lambda_f2 = float(state["lambda_F2"])
        power_p = float(state["power_p"])
        f2_value = _f2(lambda_f2, power_p)
        provenance = f"ll_gauge_action_normalization:{state['normalization_provenance']}"
        action_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "a0_matching_value": 0.125,
            "L_F2_family": "monomial_lambda_F2_power_p",
            "lambda_F2": lambda_f2,
            "power_p": power_p,
            "F2_units": "m_minus_4",
            "action_provenance": provenance,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        flux_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "flux_cycle": "S2_throat",
            "area_gauge": "physical_induced_S2_metric",
            "F2_convention": "F_ab_F^ab_equals_2_B2_over_Rs4",
            "SO3_flux_ansatz_proved": True,
            "flux_quantization_proved": True,
            "flux_integer_n": int(state["flux_integer_n"]),
            "q_LL_dimensionless": float(state["q_LL_dimensionless"]),
            "F2_0_m_minus_4": f2_value,
            "flux_state_provenance": provenance,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            action_output_path.parent.mkdir(parents=True, exist_ok=True)
            action_output_path.write_text(
                json.dumps(action_payload, indent=2),
                encoding="utf-8",
            )
            flux_output_path.write_text(
                json.dumps(flux_payload, indent=2),
                encoding="utf-8",
            )

    return {
        "status": "janus-z2-null-sigma-llbrane-gauge-action-normalization-pipeline",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "input_exists": state is not None,
        "validation_errors": errors,
        "F2_0_m_minus_4": f2_value,
        "action_payload": action_payload,
        "flux_payload": flux_payload,
        "writes_action_input": ready,
        "writes_flux_input": ready,
        "downstream_chi_reducer_ready": ready,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_active_gauge_normalization_manifest",
            "include q_LL, lambda_F2, power_p, flux_integer_n, and physical area gauge",
            "prove normalization without observational or legacy provenance",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Gauge Action Normalization Pipeline",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Downstream chi reducer ready: `{payload['downstream_chi_reducer_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
