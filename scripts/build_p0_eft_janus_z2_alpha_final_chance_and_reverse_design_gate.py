from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "alpha_reverse_design_inputs.json"
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_alpha_final_chance_and_reverse_design_gate.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_alpha_final_chance_and_reverse_design_gate.md"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def required_mass_for_alpha(alpha_m: float, c_m_s: float, g_si: float) -> float:
    if alpha_m <= 0.0 or c_m_s <= 0.0 or g_si <= 0.0:
        raise ValueError("alpha_m, c_m_s and g_si must be positive")
    return alpha_m * c_m_s**2 / (2.0 * math.pi * g_si)


def required_charge_unit_for_alpha(
    *, alpha_m: float, integer_n: int, c_m_s: float, g_si: float
) -> float:
    if integer_n == 0:
        raise ValueError("integer_n must be nonzero")
    return required_mass_for_alpha(alpha_m, c_m_s, g_si) / abs(integer_n)


def _target_block(data: dict[str, Any]) -> dict[str, Any]:
    if "published_alpha_m" not in data:
        return {
            "target_alpha_available": False,
            "required_boundary_mass_kg": None,
            "required_charge_unit_kg_for_n": None,
            "target_compatibility_decidable": False,
        }
    alpha = float(data["published_alpha_m"])
    c = float(data.get("c_m_s", 299792458.0))
    g = float(data.get("G_SI", 6.67430e-11))
    n = int(data.get("integer_n", 1))
    return {
        "target_alpha_available": True,
        "published_alpha_m": alpha,
        "integer_n": n,
        "required_boundary_mass_kg": required_mass_for_alpha(alpha, c, g),
        "required_charge_unit_kg_for_n": required_charge_unit_for_alpha(
            alpha_m=alpha, integer_n=n, c_m_s=c, g_si=g
        ),
        "target_compatibility_decidable": True,
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    routes = [
        {
            "id": "derive_alpha_from_global_Janus_PT_charge",
            "best_formula": "alpha = 2*pi*G*|M_PT|/c^2",
            "current_status": "blocked",
            "blocker": "M_PT is a conserved state charge but no Janus/PT theorem fixes its value.",
            "would_close_if": "boundary Hamiltonian or Noether charge is derived with a fixed non-observational value",
        },
        {
            "id": "derive_sector_quantization",
            "best_formula": "alpha_n = 2*pi*G*|n|*m_charge/c^2",
            "current_status": "blocked",
            "blocker": "missing mass/charge unit and primitive-sector selection law",
            "would_close_if": "PT/Souriau prequantization gives a mass lattice and Janus selects primitive n",
        },
        {
            "id": "derive_global_bimetric_state_law_for_E_global",
            "best_formula": "E_global -> rho_plus0_abs -> alpha sector normalization",
            "current_status": "blocked",
            "blocker": "published equations admit a conserved E, but current assets do not select its value",
            "would_close_if": "the bimetric action supplies a vacuum/state law fixing E_global before observation",
        },
        {
            "id": "observational_unique_alpha_sector",
            "best_formula": "posterior P(alpha|non-compressed data) has one stable sector",
            "current_status": "conditional_not_no_fit",
            "blocker": "this can select our universe's state sector but does not derive alpha internally",
            "would_close_if": "a declared alpha-state model is tested against real non-compressed data with no hidden priors",
        },
    ]
    reverse_designs = [
        {
            "id": "boundary_charge_law",
            "new_law_needed": "Janus/PT Hamiltonian boundary charge has a fixed vacuum value",
            "meaning": "alpha is a global mass/energy charge of the resolved projective tunnel",
            "new_axiom_risk": "medium unless derived from the master action and boundary conditions",
        },
        {
            "id": "PT_Souriau_prequantization_law",
            "new_law_needed": "Omega_PT/(2*pi*hbar) has integral periods and a primitive sector",
            "meaning": "alpha is discrete; our universe is one charge sector",
            "new_axiom_risk": "medium/high unless the PT phase space and mass moment-map period are explicit",
        },
        {
            "id": "bimetric_vacuum_state_law",
            "new_law_needed": "the two-sector action fixes E_global by a vacuum or regularity condition",
            "meaning": "alpha is not local throat data, but the global bimetric state energy",
            "new_axiom_risk": "medium unless the law follows from the published field equations",
        },
        {
            "id": "quantum_geometry_area_or_flux_law",
            "new_law_needed": "A_Sigma or flux through Sigma is quantized and mapped to alpha",
            "meaning": "alpha is UV/geometric, not classical cosmological",
            "new_axiom_risk": "high unless Janus supplies the quantum area/flux unit",
        },
        {
            "id": "observational_sector_selection",
            "new_law_needed": "none, but alpha is treated as an initial/state parameter",
            "meaning": "the theory is a sector family; data identify our sector",
            "new_axiom_risk": "low, but no no-fit claim",
        },
    ]
    return {
        "status": "janus-z2-alpha-final-chance-and-reverse-design-gate",
        "active_core": "Z2_tunnel_Sigma",
        "direct_routes": routes,
        "direct_internal_alpha_derivation_available": False,
        "best_honest_current_use": "alpha_as_explicit_state_sector",
        "reverse_design_options": reverse_designs,
        "target_alpha_matching": _target_block(data),
        "final_verdict": (
            "No current Janus/Z2/Sigma asset derives alpha internally. To make "
            "the model stronger than published Janus, one must add or derive a "
            "state-selection law: boundary charge, PT/Souriau quantization, "
            "bimetric vacuum energy, or quantum geometry. Observation can select "
            "a sector but cannot turn the state parameter into a no-fit theorem."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Alpha Final Chance And Reverse Design Gate",
                "",
                f"Internal alpha derivation available: `{payload['direct_internal_alpha_derivation_available']}`",
                f"Best honest current use: `{payload['best_honest_current_use']}`",
                "",
                payload["final_verdict"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
