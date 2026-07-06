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
from scripts.build_p0_eft_janus_z2_sigma_distribution_isotropy_anisotropic_stress_gate import (
    build_payload as build_isotropy_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_fermion_distribution_of_a_gate import (
    build_payload as build_distribution_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_kinetic_moment_fluid_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_kinetic_moment_fluid_closure_gate.json")


def build_payload() -> dict:
    distribution = build_distribution_payload()
    dirac_eos = build_dirac_eos_payload()
    isotropy = build_isotropy_payload()
    declared = {
        "kinetic_moment_bibliography_checked": True,
        "stress_energy_moment_formula_declared": True,
        "Dirac_equation_of_state_gate_declared": True,
        "fermion_distribution_gate_declared": True,
        "distribution_isotropy_anisotropic_stress_gate_declared": True,
        "plus_moment_stress_declared": True,
        "minus_moment_stress_declared": True,
        "FLRW_isotropy_guard_declared": True,
        "anisotropic_stress_guard_declared": True,
        "Z2Sigma_projected_fluid_moment_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_distribution_ready": distribution["closure"]["plus_fermion_distribution_of_a_ready"],
        "minus_distribution_ready": distribution["closure"]["minus_fermion_distribution_of_a_ready"],
        "plus_equation_of_state_ready": dirac_eos["closure"]["plus_equation_of_state_derived"],
        "minus_equation_of_state_ready": dirac_eos["closure"]["minus_equation_of_state_derived"],
        "plus_FLRW_isotropy_derived": isotropy["closure"]["plus_anisotropic_stress_zero_derived"],
        "minus_FLRW_isotropy_derived": isotropy["closure"]["minus_anisotropic_stress_zero_derived"],
        "plus_fluid_moment_ready": False,
        "minus_fluid_moment_ready": False,
        "projected_fluid_moment_ready": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none"
    if not ready:
        if not distribution["gate_passed"]:
            primary_blocker = distribution["primary_blocker"]
        elif not dirac_eos["gate_passed"]:
            primary_blocker = dirac_eos["primary_blocker"]
        elif not isotropy["gate_passed"]:
            primary_blocker = isotropy["primary_blocker"]
        else:
            primary_blocker = "kinetic_moment_projection"
    return {
        "status": "janus-z2-sigma-kinetic-moment-fluid-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Ma/Bertschinger massive-neutrino stress-energy moments",
            "relativistic kinetic/Vlasov stress-energy moment literature",
            "standard FLRW perfect-fluid reduction from isotropic distributions",
            "Janus Z2/Sigma distribution isotropy and anisotropic-stress gate",
        ],
        "bibliography_result": (
            "Primary kinetic theory supplies T_munu[f] moments and rho/p extraction. "
            "The active Janus Z2/Sigma model must still prove isotropy and absence "
            "of anisotropic stress for the projected FLRW sector."
        ),
        "source_links": [
            "https://arxiv.org/pdf/astro-ph/9506072",
            "https://pmc.ncbi.nlm.nih.gov/articles/PMC5253932/",
            "https://ned.ipac.caltech.edu/level5/March02/Bertschinger/Bert3.html",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "fermion_distribution_of_a": {
                "gate_passed": distribution["gate_passed"],
                "primary_blocker": distribution["primary_blocker"],
            },
            "dirac_equation_of_state": {
                "gate_passed": dirac_eos["gate_passed"],
                "primary_blocker": dirac_eos["primary_blocker"],
            },
            "distribution_isotropy_anisotropic_stress": {
                "gate_passed": isotropy["gate_passed"],
                "primary_blocker": isotropy["primary_blocker"],
            },
        },
        "formulas": {
            "moment_stress": "T_munu^(pm)[f] = integral dP p_mu p_nu f_pm",
            "rho_pressure": "rho_pm and p_pm are zeroth/second isotropic moments of f_pm",
            "flrw_guard": "perfect-fluid form valid only after isotropic momentum distribution is derived",
            "projection": "T_fluid^Z2Sigma = P_Z2Sigma(T_+[f_+], T_-[f_-])",
        },
        "kinetic_moment_fluid_closure_ledger_declared": all(declared.values()),
        "kinetic_moment_fluid_closure_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_fermion_distribution_of_a_gate",
            "pass_Dirac_equation_of_state_of_a_gate",
            "derive_plus_minus_FLRW_isotropy",
            "pass_distribution_isotropy_anisotropic_stress_gate",
            "prove_or_record_anisotropic_stress",
            "feed_result_to_sector_density_pressure_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Kinetic Moment Fluid Closure Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['kinetic_moment_fluid_closure_ledger_declared']}`",
        f"Fluid closure ready: `{payload['kinetic_moment_fluid_closure_ready']}`",
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
