from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_dirac_equation_of_state_of_a_gate import (
    build_payload as build_dirac_eos_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_kinetic_moment_fluid_closure_gate import (
    build_payload as build_kinetic_closure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate.json")


def build_payload() -> dict:
    dirac_eos = build_dirac_eos_payload()
    kinetic_closure = build_kinetic_closure_payload()
    declared = {
        "Janus_bimetric_FLRW_bibliography_checked": True,
        "perfect_fluid_continuity_imported": True,
        "plus_sector_rho_p_declared": True,
        "minus_sector_rho_p_declared": True,
        "Dirac_equation_of_state_gate_declared": True,
        "kinetic_moment_fluid_closure_gate_declared": True,
        "Z2_sign_policy_declared": True,
        "equation_of_state_policy_declared": True,
        "observational_fit_forbidden": True,
        "plus_continuity_equation_declared": True,
        "minus_continuity_equation_declared": True,
    }
    closure = {
        "plus_equation_of_state_derived": dirac_eos["closure"][
            "plus_equation_of_state_derived"
        ],
        "minus_equation_of_state_derived": dirac_eos["closure"][
            "minus_equation_of_state_derived"
        ],
        "plus_initial_normalization_derived": False,
        "minus_initial_normalization_derived": False,
        "plus_fluid_moment_ready": kinetic_closure["closure"]["plus_fluid_moment_ready"],
        "minus_fluid_moment_ready": kinetic_closure["closure"]["minus_fluid_moment_ready"],
        "plus_rho_p_of_a_ready": dirac_eos["closure"]["plus_equation_of_state_derived"]
        and kinetic_closure["closure"]["plus_fluid_moment_ready"],
        "minus_rho_p_of_a_ready": dirac_eos["closure"]["minus_equation_of_state_derived"]
        and kinetic_closure["closure"]["minus_fluid_moment_ready"],
    }
    return {
        "status": "janus-z2-sigma-sector-density-pressure-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Petit/Margnat/Zejli 2024, arXiv:2412.04644",
            "standard FLRW perfect-fluid continuity equation",
            "Janus bimetric FLRW sector literature",
            "active Dirac equation-of-state gate",
            "active kinetic moment fluid-closure gate",
        ],
        "bibliography_result": (
            "Standard FLRW gives rho' + 3H(rho+p)=0 and perfect-fluid stress. "
            "Janus literature supplies plus/minus FLRW sectors. The active Z2/Sigma "
            "model must derive sector equations of state and normalizations; they are "
            "not imported from compressed observational fits."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "dirac_equation_of_state": {
                "gate": dirac_eos["status"],
                "ready": dirac_eos["dirac_equation_of_state_ready"],
                "primary_blocker": dirac_eos["primary_blocker"],
                "closure": dirac_eos["closure"],
            },
            "kinetic_moment_fluid_closure": {
                "gate": kinetic_closure["status"],
                "ready": kinetic_closure["kinetic_moment_fluid_closure_ready"],
                "primary_blocker": kinetic_closure["primary_blocker"],
                "closure": kinetic_closure["closure"],
            },
        },
        "formulas": {
            "continuity_plus": "d rho_+/d ln a + 3(rho_+ + p_+) = 0",
            "continuity_minus": "d rho_-/d ln a + 3(rho_- + p_-) = 0",
            "constant_w_solution": "rho_pm(a) = rho_pm0 * a^(-3(1+w_pm)) only after w_pm is derived",
            "sign_policy": "Z2 gravitational sign is separate from thermodynamic rho_pm sign",
        },
        "sector_density_pressure_ledger_declared": all(declared.values()),
        "sector_density_pressure_of_a_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else (
                dirac_eos["primary_blocker"]
                if not dirac_eos["dirac_equation_of_state_ready"]
                else kinetic_closure["primary_blocker"]
            )
        ),
        "next_required": [
            "derive_plus_sector_equation_of_state",
            "derive_minus_sector_equation_of_state",
            "pass_Dirac_equation_of_state_of_a_gate",
            "pass_kinetic_moment_fluid_closure_gate",
            "derive_sector_normalizations_from_action_or_topology",
            "propagate_rho_p_plus_minus_to_bulk_stress_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Sector Density/Pressure Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['sector_density_pressure_ledger_declared']}`",
        f"Sector rho/p ready: `{payload['sector_density_pressure_of_a_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
