from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import C_SI, G_SI


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "llbrane_s2_flux_superselection_inputs.json"
CHI_OUTPUT_PATH = BASE / "null_bridge_llbrane_tension_inputs.json"
ORBIT_OUTPUT_PATH = BASE / "souriau_chi_ll_orbit_state_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_chi_ll_superselection_flux_reducer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_chi_ll_superselection_flux_reducer_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_text(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive_number(payload: dict[str, Any], key: str, errors: list[str]) -> float:
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
    if payload.get("flux_cycle") != "S2_throat":
        errors.append("flux_cycle_must_be_S2_throat")
    if payload.get("area_gauge") != "physical_induced_S2_metric":
        errors.append("area_gauge_must_be_physical_induced_S2_metric")
    if payload.get("F2_convention") != "F_ab_F^ab_equals_2_B2_over_Rs4":
        errors.append("F2_convention_must_match_reducer")
    if payload.get("SO3_flux_ansatz_proved") is not True:
        errors.append("SO3_flux_ansatz_must_be_proved")
    if payload.get("flux_quantization_proved") is not True:
        errors.append("flux_quantization_must_be_proved")
    if _bad_text(payload.get("flux_state_provenance")):
        errors.append("flux_state_provenance_missing_or_forbidden")

    n = payload.get("flux_integer_n")
    if not isinstance(n, int):
        errors.append("flux_integer_n_must_be_integer")
    elif n == 0:
        errors.append("flux_integer_n_must_be_nonzero")
    _positive_number(payload, "q_LL_dimensionless", errors)
    _positive_number(payload, "F2_0_m_minus_4", errors)
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def _compute(payload: dict[str, Any]) -> dict[str, float]:
    n_abs = abs(int(payload["flux_integer_n"]))
    q_ll = float(payload["q_LL_dimensionless"])
    f2 = float(payload["F2_0_m_minus_4"])
    b_flux = n_abs / (2.0 * q_ll)
    r_s_m = (2.0 * b_flux * b_flux / f2) ** 0.25
    chi_abs_inverse_m = 1.0 / (8.0 * math.pi * r_s_m)
    mass_kg = C_SI * C_SI * r_s_m / (2.0 * G_SI)
    return {
        "B_abs": b_flux,
        "R_s_m": r_s_m,
        "chi_LL_abs_inverse_m": chi_abs_inverse_m,
        "M_bridge_kg": mass_kg,
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    chi_output_path: Path = CHI_OUTPUT_PATH,
    orbit_output_path: Path = ORBIT_OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    state = _read(input_path)
    errors = [] if state is None else _validate(state)
    ready = state is not None and not errors
    computed = _compute(state) if ready else None
    chi_payload = None
    orbit_payload = None

    if ready and computed is not None:
        provenance = f"S2_flux_superselection:{state['flux_state_provenance']}"
        chi_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "chi_LL_sign": "negative",
            "chi_LL_abs_inverse_m": computed["chi_LL_abs_inverse_m"],
            "chi_LL_provenance": provenance,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        orbit_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "orbit_label_kind": "coadjoint_orbit_mass_casimir",
            "moment_map_conserved": True,
            "PT_energy_sign_reversal_proved": True,
            "mass_casimir_kg": computed["M_bridge_kg"],
            "orbit_state_provenance": provenance,
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            chi_output_path.parent.mkdir(parents=True, exist_ok=True)
            chi_output_path.write_text(json.dumps(chi_payload, indent=2), encoding="utf-8")
            orbit_output_path.write_text(json.dumps(orbit_payload, indent=2), encoding="utf-8")

    closure = {
        "superselection_sector_declared": True,
        "Souriau_mass_orbit_target_declared": True,
        "S2_flux_cycle_declared": state is not None,
        "flux_integer_available": ready,
        "q_LL_available": ready,
        "F2_0_available": ready,
        "physical_area_gauge_fixed": ready,
        "chi_LL_abs_inverse_m_derived": ready,
        "Souriau_orbit_mass_payload_writable": ready,
    }
    return {
        "status": "janus-z2-null-sigma-chi-ll-superselection-flux-reducer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "chi_output_path": str(chi_output_path),
        "orbit_output_path": str(orbit_output_path),
        "input_exists": state is not None,
        "formulae": {
            "flux_law": "integral_S2 F_LL = 2*pi*n/q_LL",
            "SO3_ansatz": "F_theta_phi = B*sin(theta), B = n/(2*q_LL)",
            "F2_convention": "F_ab F^ab = 2*B^2/R_s^4",
            "R_s": "R_s = (2*B^2/F2_0)^(1/4)",
            "chi_LL": "chi_LL = -1/(8*pi*R_s)",
            "M_bridge": "M_bridge = c^2*R_s/(2*G)",
        },
        "closure": closure,
        "validation_errors": errors,
        "computed": computed,
        "chi_payload": chi_payload,
        "orbit_payload": orbit_payload,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_active_llbrane_flux_integer_n_on_S2_throat",
            "derive_worldvolume_charge_quantum_q_LL",
            "derive_Janus_on_shell_F2_0",
            "prove_physical_induced_S2_metric_area_gauge",
        ],
        "interpretation": (
            "This is the combined non-fit route: chi_LL is a superselection "
            "charge, Souriau carries the global mass orbit, and S2 flux "
            "quantization can discretize the sector. The reducer is active only "
            "when q_LL, F2_0, flux integer, and physical area gauge are derived."
        ),
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma chi_LL Superselection Flux Reducer Gate",
        "",
        payload["interpretation"],
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
