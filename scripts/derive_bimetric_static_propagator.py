from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
Q2 = sp.symbols("q2", positive=True)
KP, KM, MU = sp.symbols("K_plus K_minus mu", positive=True)


def operator() -> sp.Matrix:
    return sp.Matrix([[KP * Q2 + MU, -MU], [-MU, KM * Q2 + MU]])


def pole_data() -> dict[str, sp.Expr | sp.Matrix]:
    mass2 = sp.factor(MU * (KP + KM) / (KP * KM))
    massless = sp.ones(2, 2) / (KP + KM)
    massive = sp.Matrix([[KM / KP, -1], [-1, KP / KM]]) / (KP + KM)
    propagator = sp.simplify(massless / Q2 + massive / (Q2 + mass2))
    return {
        "mass2": mass2,
        "massless_residue": massless,
        "massive_residue": massive,
        "propagator": propagator,
    }


def matrix_text(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(sp.factor(value)) for value in row] for row in matrix.tolist()]


def build_payload() -> dict:
    data = pole_data()
    inverse = sp.simplify(operator().inv())
    return {
        "artifact": "bimetric_static_propagator",
        "status": "massless_and_massive_poles_with_yukawa_matrix_derived",
        "fit_used": False,
        "massive_pole_mass2": str(data["mass2"]),
        "massless_residue": matrix_text(data["massless_residue"]),
        "massive_residue": matrix_text(data["massive_residue"]),
        "inverse_matches_pole_decomposition": sp.simplify(inverse - data["propagator"]) == sp.zeros(2),
        "inverse_identity": sp.simplify(operator() * data["propagator"]) == sp.eye(2),
        "static_kernel": "G(r)=[R0+Rm*exp(-m*r)]/(4*pi*r)",
        "potential": "V(r)=-J1^T*[R0+Rm*exp(-m*r)]*J2/(4*pi*r)",
        "same_plus_yukawa_ratio": str(sp.factor(KM / KP)),
        "cross_yukawa_ratio": "-1",
        "limits": {
            "large_distance": "only massless residue R0 survives",
            "short_distance": "R0+Rm=diag(1/K_plus,1/K_minus)",
        },
        "scope": "conserved static source kernel; full spin-2 projector and Vainshtein screening remain open",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_static_propagator.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
