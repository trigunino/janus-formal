from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
B1, B2, B3 = sp.symbols("beta1 beta2 beta3")
Q2 = sp.symbols("q2", positive=True)


def coefficients() -> dict[str, sp.Expr]:
    a1 = B1 + 2 * B2 + B3
    a2 = B2 + B3
    reverse_a2 = B1 + B2

    c2_plus = a1**2 / 8
    c3_plus = a1 * a2 / 2
    c2_minus = Q2 * a1**2 / 8
    c3_minus_rho = Q2 * a1 * reverse_a2 / 2
    # Galileon duality in D=4: p3 = 2 c2 - c3.
    c3_minus_pi = 2 * c2_minus - c3_minus_rho
    c2 = sp.factor(c2_plus + c2_minus)
    c3 = sp.factor(c3_plus + c3_minus_pi)
    return {
        "c2_plus": c2_plus,
        "c3_plus": c3_plus,
        "c2_minus": c2_minus,
        "c3_minus_rho": c3_minus_rho,
        "c3_minus_pi": sp.factor(c3_minus_pi),
        "C2": c2,
        "C3": c3,
    }


def build_payload() -> dict:
    raw = coefficients()
    b1, b2 = sp.symbols("b1 b2", positive=True)
    pt = {key: sp.factor(value.subs({B1: b1, B2: b2, B3: b1})) for key, value in raw.items()}
    s = b1 + b2
    expected_c2 = s**2 * (1 + Q2) / 2
    expected_c3 = s**2
    # L2=pi U1=6 pi Box(pi), so phi=sqrt(12 C2) pi.
    g3 = sp.factor(expected_c3 / (12 * expected_c2) ** sp.Rational(3, 2))
    return {
        "artifact": "bimetric_canonical_vainshtein_coefficient",
        "convention": "Lambda3^3*(C2 L2 + C3 L3), L_n=pi U_(n-1), q2=K_plus/K_minus",
        "general": {key: str(value) for key, value in raw.items()},
        "pt_branch": {
            "C2": str(pt["C2"]),
            "C3": str(pt["C3"]),
            "minus_frame_cubic_after_duality": str(pt["c3_minus_pi"]),
            "canonical_field": "phi=sqrt(12*C2)*pi",
            "canonical_cubic_g3": str(g3),
        },
        "closure": {
            "both_bigravity_frames_combined": True,
            "pt_dual_frame_cubic_cancels": sp.simplify(pt["c3_minus_pi"]) == 0,
            "pt_kinetic_identity": sp.simplify(pt["C2"] - expected_c2) == 0,
            "pt_cubic_identity": sp.simplify(pt["C3"] - expected_c3) == 0,
            "source_charge_still_required_for_numeric_rV": True,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_canonical_vainshtein_coefficient.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
