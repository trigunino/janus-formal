from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_phase_kernel.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_phase_kernel.json")
QUAD_IDENTITY_PATH = Path("outputs/reports/p0_eft_janus_z4_tight_coupling_quadrupole_identity.json")


def _load_quadrupole_identity() -> dict:
    if not QUAD_IDENTITY_PATH.exists():
        return {}
    return json.loads(QUAD_IDENTITY_PATH.read_text(encoding="utf-8"))


def build_payload() -> dict:
    quadrupole_identity = _load_quadrupole_identity()
    theta0, vb, psi, theta2, e2 = sp.symbols("Theta0 vb Psi Theta2 E2")
    k, tau_dot, ell = sp.symbols("k tau_dot ell", nonzero=True)
    p0, pd, pq, pe, pz = sp.symbols("p_0 p_D p_Q p_E p_Z")
    q_z4 = sp.symbols("Q_Z4")

    temperature_source = theta0 + psi + pd * vb
    polarization_source = pq * theta2 + pe * e2 + pz * q_z4
    physical_quadrupole_phase = sp.expand(theta2 - k * vb / tau_dot)

    te_phase_kernel = sp.expand(polarization_source - theta2)
    no_z4_free_phase = sp.diff(polarization_source, q_z4)
    no_monopole_leakage = sp.diff(polarization_source, theta0)
    no_potential_leakage = sp.diff(polarization_source, psi)
    temperature_doppler_residual = sp.expand(sp.diff(temperature_source, vb) - pd)

    closure_solution = sp.solve(
        [
            sp.Eq(pq - 1, 0),
            sp.Eq(pe, 0),
            sp.Eq(pz, 0),
            sp.Eq(pd - 1, 0),
        ],
        [pq, pe, pz, pd],
        dict=True,
    )
    solution = closure_solution[0] if len(closure_solution) == 1 else {}
    substituted = {
        "te_phase_kernel": str(sp.simplify(te_phase_kernel.subs(solution))),
        "no_z4_free_phase": str(sp.simplify(no_z4_free_phase.subs(solution))),
        "no_monopole_leakage": str(sp.simplify(no_monopole_leakage.subs(solution))),
        "no_potential_leakage": str(sp.simplify(no_potential_leakage.subs(solution))),
        "temperature_doppler_residual": str(sp.simplify(temperature_doppler_residual.subs(solution))),
        "tight_coupling_quadrupole_identity": str(physical_quadrupole_phase),
    }

    unresolved = {
        "quadrupole_velocity_phase_relation": str(physical_quadrupole_phase),
        "required_identity": "Theta2 = k*vb/tau_dot from the Z4 tight-coupling quadrupole equation",
    }

    return {
        "status": "janus-z4-acoustic-polarization-phase-kernel",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "variables_isolated": ["Theta0", "vb", "Psi", "Theta2", "E2", "Q_Z4"],
        "kernel_coefficients": ["p_0", "p_D", "p_Q", "p_E", "p_Z"],
        "temperature_source": str(temperature_source),
        "polarization_source": str(polarization_source),
        "residuals": {
            "te_phase_kernel": str(te_phase_kernel),
            "no_z4_free_phase": str(no_z4_free_phase),
            "no_monopole_leakage": str(no_monopole_leakage),
            "no_potential_leakage": str(no_potential_leakage),
            "temperature_doppler_residual": str(temperature_doppler_residual),
        },
        "formal_closure_solution": [{str(k): str(v) for k, v in row.items()} for row in closure_solution],
        "residuals_after_substitution": substituted,
        "algebraic_phase_kernel_ready": True,
        "tight_coupling_quadrupole_identity_derived": bool(
            quadrupole_identity.get("tight_coupling_quadrupole_identity_derived")
        ),
        "requires_tight_coupling_quadrupole_identity": not bool(
            quadrupole_identity.get("tight_coupling_quadrupole_identity_derived")
        ),
        "quadrupole_identity_report_used": bool(quadrupole_identity),
        "unresolved_physical_identity": unresolved,
        "observational_planck_gate_passed": False,
        "verdict": (
            "The phase kernel isolates the next required physics: TE cannot be fixed by an E-mode "
            "amplitude scale. A Z4 tight-coupling quadrupole identity must derive the phase relation "
            "Theta2 = k*vb/tau_dot while keeping Q_Z4 out of the polarization source."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Acoustic/Polarization Phase Kernel",
        "",
        f"Status: `{payload['status']}`",
        f"Solver numerics modified: `{payload['solver_numerics_modified']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Algebraic phase kernel ready: `{payload['algebraic_phase_kernel_ready']}`",
        f"Tight-coupling quadrupole identity derived: `{payload['tight_coupling_quadrupole_identity_derived']}`",
        "",
        "## Formal Closure Solution",
    ]
    for row in payload["formal_closure_solution"]:
        lines.append(f"- `{row}`")
    lines.extend(["", "## Residuals After Substitution"])
    for key, value in payload["residuals_after_substitution"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        "## Quadrupole Identity",
        f"- report used: `{payload['quadrupole_identity_report_used']}`",
        f"- still required: `{payload['requires_tight_coupling_quadrupole_identity']}`",
        f"- identity: `{payload['unresolved_physical_identity']['required_identity']}`",
        "",
        payload["verdict"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
