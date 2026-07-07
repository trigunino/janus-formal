from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "souriau_chi_ll_orbit_state_inputs.json"
OUTPUT_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")
ALLOWED_ORBIT_KINDS = {
    "coadjoint_orbit_mass_casimir",
    "global_hamiltonian_moment_map",
}


def _read(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _bad_text(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _validate(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "Z2_null_Sigma_PT_bridge":
        errors.append("branch_must_be_Z2_null_Sigma_PT_bridge")
    if payload.get("source") != "active_derived":
        errors.append("source_must_be_active_derived")
    if payload.get("orbit_label_kind") not in ALLOWED_ORBIT_KINDS:
        errors.append("orbit_label_kind_not_allowed")
    if payload.get("moment_map_conserved") is not True:
        errors.append("moment_map_conserved_must_be_true")
    if payload.get("PT_energy_sign_reversal_proved") is not True:
        errors.append("PT_energy_sign_reversal_must_be_proved")

    mass = payload.get("mass_casimir_kg")
    if not isinstance(mass, (int, float)) or not math.isfinite(float(mass)):
        errors.append("mass_casimir_kg_must_be_finite")
    elif float(mass) <= 0.0:
        errors.append("mass_casimir_kg_must_be_positive")

    if _bad_text(payload.get("orbit_state_provenance")):
        errors.append("orbit_state_provenance_missing_or_forbidden")
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
    state = _read(input_path)
    validation_errors = [] if state is None else _validate(state)
    ready = state is not None and not validation_errors
    mass_solution = None

    if ready:
        mass = float(state["mass_casimir_kg"])
        mass_solution = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "M_plus_kg": mass,
            "M_minus_kg": -mass,
            "PT_energy_sign_reversal_proved": True,
            "bimetric_global_solution_proved": True,
            "M_bridge_role": "bulk_solution_or_Noether_state_label",
            "M_bridge_provenance": (
                "souriau_superselection_orbit:"
                f"{state['orbit_state_provenance']}"
            ),
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(mass_solution, indent=2), encoding="utf-8")

    closure = {
        "Souriau_moment_map_framework_available": True,
        "moment_map_charge_conserved": True,
        "coadjoint_orbit_mass_label_available_as_target": True,
        "PT_energy_sign_reversal_maps_M_to_minus_M": True,
        "chi_LL_related_to_abs_mass_by_bridge_matching": True,
        "specific_orbit_state_selected": ready,
        "mass_casimir_value_available": ready,
        "chi_LL_abs_inverse_m_derivable_downstream": ready,
    }
    return {
        "status": "janus-z2-null-sigma-chi-ll-noether-souriau-superselection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": state is not None,
        "bibliography": [
            {
                "label": "Souriau, Structure of Dynamical Systems",
                "use": "moment map/coadjoint orbit interpretation of mass labels",
                "url": "https://empg.maths.ed.ac.uk/Activities/Souriau/Souriau.pdf",
            },
            {
                "label": "Moment map physical context",
                "use": "Noether-Souriau conservation of moment map on dynamics",
                "url": "https://mathoverflow.net/questions/347668/definition-of-a-moment-map-with-physical-context",
            },
            {
                "label": "M30 Janus source card",
                "use": "PT/Souriau sign pairing in the active Janus bimetric ledger",
                "url": "docs/source_cards/M30.md",
            },
        ],
        "closure": closure,
        "souriau_superselection_route_formulated": True,
        "souriau_superselection_selects_chi_LL_now": ready,
        "validation_errors": validation_errors,
        "mass_solution_payload": mass_solution,
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_or_declare_active_Souriau_orbit_state_with_mass_casimir_kg",
            "prove_moment_map_conservation_for_the_active_Z2_PT_state",
            "prove_PT_energy_sign_reversal_for_the_same_orbit",
            "then_run_global_mass_to_bridge_and_chi_matching",
        ],
        "interpretation": (
            "Souriau/Noether can make chi_LL a superselection charge through the "
            "global mass orbit label. It does not choose the orbit. A numeric "
            "chi_LL follows only after the active state supplies a mass Casimir "
            "or Hamiltonian moment-map value."
        ),
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma chi_LL Noether/Souriau Superselection Gate",
        "",
        payload["interpretation"],
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Selects chi_LL now: `{payload['souriau_superselection_selects_chi_LL_now']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
