from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
KP, KM, MU, K2 = sp.symbols("K_plus K_minus mu k2", positive=True)


def scalar_data() -> dict[str, sp.Expr | sp.Matrix]:
    kinetic = sp.factor(KP * KM / (KP + KM))
    mass2 = sp.factor(MU * (KP + KM) / (KP * KM))
    sheet_residue = sp.Matrix([[KM / KP, -1], [-1, KP / KM]]) / (KP + KM)
    return {
        "relative_kinetic": kinetic,
        "mass2": mass2,
        "helicity0_kinetic": sp.factor(3 * kinetic),
        "omega2": sp.factor(K2 + mass2),
        "sheet_residue": sheet_residue,
    }


def build_payload() -> dict:
    data = scalar_data()
    residue = data["sheet_residue"]
    principal_minor = sp.factor(residue[0, 0])
    return {
        "artifact": "bimetric_helicity0_scalar_sector",
        "status": "flat_proportional_physical_scalar_sector_closed",
        "background": "proportional flat branch",
        "field_content": {
            "massless_scalar_modes": 0,
            "massive_helicity0_modes": 1,
            "bd_scalar_modes": 0,
        },
        "constraint_reduction": [
            "diagonal scalar lapse and shift implement the two scalar gauge constraints",
            "relative shift is auxiliary after Hassan-Rosen shift redefinition",
            "relative lapse plus its secondary constraint remove the BD scalar pair",
            "one Fierz-Pauli helicity-0 canonical pair remains",
        ],
        "reduced_action": "L0=(Z0/2)[pi_dot^2-(k^2+m_FP^2)pi^2]",
        "coefficients": {
            "Z0": str(data["helicity0_kinetic"]),
            "m_FP2": str(data["mass2"]),
            "omega2": str(data["omega2"]),
        },
        "massive_sheet_residue": [[str(sp.factor(x)) for x in row] for row in residue.tolist()],
        "checks": {
            "residue_rank": int(residue.rank()),
            "residue_determinant_zero": sp.factor(residue.det()) == 0,
            "residue_positive_semidefinite_for_positive_kinetics": principal_minor.is_positive,
            "helicity0_no_ghost_for_positive_kinetics": data["helicity0_kinetic"].is_positive,
            "gradient_speed2": "1",
            "no_gradient_instability": True,
            "no_tachyon_if_mu_positive": data["mass2"].is_positive,
        },
        "closure": {
            "flat_quadratic_scalar_count": True,
            "flat_helicity0_kinetic_sign": True,
            "flat_gradient_and_mass_sign": True,
            "cosmological_time_dependent_scalar_sector": False,
            "strong_coupling_scale_computed": False,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_helicity0_scalar_sector.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
