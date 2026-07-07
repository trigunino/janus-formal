from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "exact_solution_alpha_state_sector_inputs.json"
OUTPUT_PATH = BASE / "published_exact_solution_scale_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_exact_solution_alpha_state_sector_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_exact_solution_alpha_state_sector_gate.json"
)
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0.0


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN)


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    errors = ["missing_exact_solution_alpha_state_sector_inputs"] if data is None else []
    output = None
    if data is not None:
        if data.get("active_core") != "Z2_tunnel_Sigma":
            errors.append("active_core_must_be_Z2_tunnel_Sigma")
        if data.get("source") != "exact_solution_integration_constant_state":
            errors.append("source_must_be_exact_solution_integration_constant_state")
        if _bad_provenance(data.get("alpha_state_provenance")):
            errors.append("alpha_state_provenance_missing_or_forbidden")
        if data.get("alpha_sector_declared_not_derived") is not True:
            errors.append("alpha_sector_must_be_declared_not_derived")
        if data.get("full_no_fit_prediction_ready") is not False:
            errors.append("full_no_fit_prediction_must_remain_false")
        for key in ["alpha_m", "c_plus0_m_s", "c_minus0_m_s", "G_plus_SI"]:
            if not _positive(data.get(key)):
                errors.append(f"{key}_missing_or_nonpositive")
        for key in [
            "observational_fit_used",
            "compressed_planck_lcdm_background_used",
            "archived_z4_reuse_used",
        ]:
            if data.get(key) is True:
                errors.append(f"forbidden_flag:{key}")
        if not errors:
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "published_exact_solution_alpha_from_state_sector",
                "scale_provenance": (
                    "exact_solution_integration_constant_state:"
                    f"{data['alpha_state_provenance']}"
                ),
                "alpha_m": float(data["alpha_m"]),
                "c_plus0_m_s": float(data["c_plus0_m_s"]),
                "c_minus0_m_s": float(data["c_minus0_m_s"]),
                "G_plus_SI": float(data["G_plus_SI"]),
                "a_plus0_weight": float(data.get("a_plus0_weight", 1.0)),
                "a_minus0_weight": float(data.get("a_minus0_weight", 1.0)),
                "alpha_is_integration_constant": True,
                "alpha_is_not_topology_prediction": True,
                "full_no_fit_prediction_ready": False,
                "observational_fit_used": False,
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
            }
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    ready = output is not None
    return {
        "status": "janus-z2-exact-solution-alpha-state-sector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": data is not None,
        "alpha_state_sector_ready": ready,
        "alpha_is_integration_constant": ready,
        "alpha_is_not_topology_prediction": ready,
        "conditional_state_prediction": ready,
        "full_no_fit_prediction_ready": False,
        "scale_payload": output,
        "validation_errors": errors,
        "remaining_blocker": "none" if ready else "alpha_state_sector_input",
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Exact Solution Alpha State Sector Gate",
        "",
        f"Ready: `{payload['alpha_state_sector_ready']}`",
        f"Conditional state prediction: `{payload['conditional_state_prediction']}`",
        f"Full no-fit prediction: `{payload['full_no_fit_prediction_ready']}`",
        f"Remaining blocker: `{payload['remaining_blocker']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
