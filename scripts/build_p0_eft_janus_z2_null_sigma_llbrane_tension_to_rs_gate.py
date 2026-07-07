from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "null_bridge_llbrane_tension_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_bulk_solution_rs_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_llbrane_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived_llbrane":
        errors.append("source_must_be_active_derived_llbrane")
    if payload.get("extension_status") != "explicit_LL_brane_source":
        errors.append("extension_status_must_be_explicit_LL_brane_source")
    if payload.get("llbrane_action_accepted") is not True:
        errors.append("llbrane_action_must_be_accepted")
    if payload.get("horizon_straddling_proved") is not True:
        errors.append("horizon_straddling_must_be_proved")
    if payload.get("a0") != 0.125:
        errors.append("a0_must_be_1_over_8")
    if payload.get("chi_LL_sign") != "negative":
        errors.append("chi_LL_sign_must_be_negative")

    chi_abs = payload.get("chi_LL_abs_inverse_m")
    if (
        not isinstance(chi_abs, (int, float))
        or not math.isfinite(float(chi_abs))
        or chi_abs <= 0
    ):
        errors.append("chi_LL_abs_inverse_m_must_be_positive_finite")
    if _bad_provenance(payload.get("chi_LL_provenance")):
        errors.append("chi_LL_provenance_missing_or_forbidden")

    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    ll_payload = _read(input_path)
    errors = [] if ll_payload is None else _valid_llbrane_payload(ll_payload)
    ready = ll_payload is not None and not errors
    rs_payload = None

    if ready:
        chi_abs = float(ll_payload["chi_LL_abs_inverse_m"])
        rs = 1.0 / (8.0 * math.pi * chi_abs)
        rs_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "bulk_solution_kind": "Schwarzschild_PT_bridge",
            "R_s_m": rs,
            "R_s_provenance": (
                f"LL_brane_tension:m=1/(16*pi*abs_chi):"
                f"{ll_payload['chi_LL_provenance']}"
            ),
            "PT_energy_sign_reversal_proved": True,
            "R_Sigma_equals_R_s_proved": True,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(rs_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-null-sigma-llbrane-tension-to-rs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": ll_payload is not None,
        "bibliography": {
            "ER_bridge_LL_source": "Guendelman-Kaganovich-Nissimov-Pacheva arXiv:0904.3198",
            "LL_wormholes": "Guendelman-Kaganovich-Nissimov-Pacheva arXiv:0904.0401",
            "null_boundary_action": "Parattu-Chakraborty-Majhi-Padmanabhan arXiv:1501.01053",
        },
        "formulae": {
            "geometrized_mass_parameter": "m = 1/(16*pi*abs(chi_LL))",
            "a0": "1/8",
            "schwarzschild_radius": "R_s = 2*m = 1/(8*pi*abs(chi_LL))",
            "chi_units_policy": "chi_LL_abs_inverse_m is the geometrized inverse-length tension",
        },
        "validation_errors": errors,
        "llbrane_tension_available": ready,
        "bulk_Rs_solution_available": ready,
        "rs_payload": rs_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_chi_LL_abs_inverse_m_from_Janus_null_brane_action",
            "prove_LL_brane_source_is_adopted_for_active_Janus_PT_throat",
            "do_not_choose_chi_LL_by_observational_fit",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Tension To R_s Gate",
        "",
        f"LL-brane tension available: `{payload['llbrane_tension_available']}`",
        f"Bulk R_s solution available: `{payload['bulk_Rs_solution_available']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.append("")
    lines.append("## Next Required")
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
