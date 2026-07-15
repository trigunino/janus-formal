from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
KP, KM, MASS2, HP, HM = sp.symbols("K_plus K_minus mass2 H_plus H_minus", positive=True)
B1, B2, B3 = sp.symbols("beta1 beta2 beta3")


def dressed_polynomial() -> sp.Expr:
    return B1 * HM**2 + 2 * B2 * HP * HM + B3 * HP**2


def generalized_higuchi_gap() -> sp.Expr:
    return sp.factor(
        sp.Rational(1, 2) * MASS2 * dressed_polynomial()
        * (HP**2 / KP + HM**2 / KM)
        - 2 * HM**3 * HP**3
    )


def proportional_gap() -> sp.Expr:
    h = sp.symbols("H", positive=True)
    return sp.factor(generalized_higuchi_gap().subs({HP: h, HM: h}) / h**4)


def build_payload() -> dict:
    return {
        "artifact": "bimetric_cosmological_higuchi_gate",
        "status": "full_two_hubble_bigravity_higuchi_gate_derived",
        "fit_used": False,
        "dressed_polynomial": str(dressed_polynomial()),
        "generalized_higuchi_gap": str(generalized_higuchi_gap()),
        "proportional_specialization_divided_by_H4": str(proportional_gap()),
        "conditions": {
            "positive_kinetics": "K_plus>0 and K_minus>0",
            "positive_hubbles": "H_plus>0 and H_minus>0",
            "helicity0_no_ghost": "Delta_bi>0",
            "strong_coupling_surface": "Delta_bi=0",
            "trajectory_condition": "inf_t Delta_bi(H_plus(t),H_minus(t))>0",
        },
        "branch_warning": "beta1*H_minus^2+2*beta2*H_plus*H_minus+beta3*H_plus^2=0 makes the dressed interaction mass vanish",
        "closure": {
            "full_two_hubble_higuchi_gate": True,
            "strong_coupling_surface_identified": True,
            "full_time_dependent_background_supplied": False,
            "trajectory_stability_decided": False,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_cosmological_higuchi_gate.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
