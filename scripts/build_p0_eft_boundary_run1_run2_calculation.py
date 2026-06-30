from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_run1_run2_calculation.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_run1_run2_calculation.json")


def solve_run1_conditions() -> dict:
    # Work in the Clifford basis {I, N=gamma^n, G=gamma5, C=N*G}.
    # Target: K*N*(I + sigma*C) = K*N + K*sigma*N*C.
    # Since N*C = N*(N*G) = eps_n*G, target coefficients are:
    # I=0, N=K, G=K*sigma*eps_n, C=0.
    return {
        "basis": "{I, N=gamma^n, G=gamma5, C=N*G}",
        "normal_square": "N^2=eps_n",
        "target": "K*N*(I + sigma*C)",
        "expanded_target": "I:0, N:K, G:K*sigma*eps_n, C:0",
        "generic_mtot": "m_I*I + m_N*N + m_G*G + m_C*C",
        "factorization_conditions": {
            "m_I": "0",
            "m_C": "0",
            "m_G": "sigma*eps_n*m_N",
            "K": "m_N",
        },
        "closed_without_physical_coefficients": False,
    }


def solve_run2_conditions() -> dict:
    return {
        "aps_operator": "A_APS=N*D_Sigma",
        "needed_commutator": "[A_APS,G]=0",
        "sufficient_geometry_conditions": [
            "D_Sigma anticommutes with G",
            "N anticommutes with G",
            "N commutes with the intrinsic spin connection used by D_Sigma",
        ],
        "zero_mode_condition": "dim ker(A_APS) = 0 mod 2",
        "ds3_warning": (
            "positive curvature can gap zero modes in compact Riemannian slices, "
            "but Lorentzian dS3 requires a precise spectral domain before this is a theorem"
        ),
        "closed_without_boundary_spectrum": False,
    }


def build_payload() -> dict:
    run1 = solve_run1_conditions()
    run2 = solve_run2_conditions()
    theorem_status = {
        "run1_symbolic_conditions_computed": True,
        "run1_factorization_proved_for_generic_coefficients": False,
        "run1_requires_physical_coefficients": True,
        "run2_sufficient_conditions_computed": True,
        "run2_commutation_proved_from_conditions": True,
        "run2_requires_actual_boundary_spectrum": True,
        "run2_zero_modes_controlled": False,
        "prediction_ready": False,
    }
    obligations = [
        "insert actual M_tot coefficients and check m_I=0, m_C=0, m_G=sigma*eps_n*m_N",
        "derive the intrinsic boundary spectrum of A_APS on the Janus Sigma geometry",
        "prove dim ker(A_APS) is zero or even",
    ]
    return {
        "description": "Bounded RUN 1/RUN 2 calculation for Janus boundary closure.",
        "status": "calculation-done-physical-inputs-still-required",
        "run1": run1,
        "run2": run2,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "RUN 1 reduces to exact Clifford coefficient equalities. RUN 2 reduces to "
            "a standard APS commutator plus a zero-mode parity check. Neither can be "
            "closed honestly without the actual boundary coefficients/spectrum."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary RUN1/RUN2 Calculation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## RUN 1 Calculation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["run1"].items())
    lines.extend(["", "## RUN 2 Calculation"])
    lines.extend(f"- {key}: {value}" for key, value in payload["run2"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
