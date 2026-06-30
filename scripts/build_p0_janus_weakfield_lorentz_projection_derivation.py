from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_lorentz_projection_derivation.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_lorentz_projection_derivation.json")
ETA = sp.diag(-1, 1, 1, 1)


def eta_skew_projection(a_matrix: sp.Matrix) -> sp.Matrix:
    return sp.simplify((a_matrix - ETA * a_matrix.T * ETA) / 2)


def eta_symmetric_part(a_matrix: sp.Matrix) -> sp.Matrix:
    return sp.simplify((a_matrix + ETA * a_matrix.T * ETA) / 2)


def scalar_weakfield_a_matrix() -> sp.Matrix:
    delta_phi, delta_psi = sp.symbols("Delta_Phi Delta_Psi")
    return sp.diag(-delta_phi, delta_psi, delta_psi, delta_psi)


def build_payload() -> dict:
    scalar_a = scalar_weakfield_a_matrix()
    scalar_f = eta_skew_projection(scalar_a)
    scalar_s = eta_symmetric_part(scalar_a)
    return {
        "description": (
            "Derivation of the Lorentz-admissible infinitesimal part of the weak-field "
            "raw solder map L_geom=I+A."
        ),
        "status": "weakfield-lorentz-projection-derived-open",
        "depends_on": [
            "p0_janus_weakfield_lgeom_lorentz_no_go_gate",
            "p0_l_k_qcross_consistency_target",
        ],
        "projection_formula": "F_eta_skew = 1/2(A - eta A^T eta)",
        "symmetric_formula": "S_eta_sym = 1/2(A + eta A^T eta)",
        "lorentz_condition_linear": "F^T eta + eta F = 0",
        "scalar_weakfield_a": [[sp.sstr(item) for item in row] for row in scalar_a.tolist()],
        "scalar_lorentz_generator_f": [[sp.sstr(item) for item in row] for row in scalar_f.tolist()],
        "scalar_symmetric_stretch_s": [[sp.sstr(item) for item in row] for row in scalar_s.tolist()],
        "derived_consequences": [
            "scalar weak-field relative potentials generate no infinitesimal Lorentz boost/rotation",
            "the diagonal L_geom mismatch is eta-symmetric stretch, not admissible Q_cross transport",
            "comoving scalar same-L branch therefore reduces to L=I at linear order",
            "non-comoving/vector/tensor branches need source-derived boost or rotation components",
        ],
        "allowed_branch": (
            "conditional comoving scalar weak-field branch: L_minus_to_plus=I, Q_cross=1, "
            "while B_4vol/Q_det and Bianchi residuals remain separate"
        ),
        "open_branch": (
            "perturbed non-comoving branch: derive F_0i/F_ij from T0i, tetrad gauge, "
            "or a Janus source connection law before using Q_cross or K transport"
        ),
        "lorentz_projection_formula_derived": True,
        "scalar_weakfield_lorentz_generator_zero": True,
        "symmetric_stretch_rejected_as_qcross": True,
        "comoving_scalar_same_l_identity_conditionally_selected": True,
        "noncomoving_boost_source_required": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Derivation improves the gate: in the scalar weak-field branch the admissible "
            "Lorentz part of L_geom is identity, not a scale factor. Any nontrivial "
            "same-L Q_cross/K transport must come from source-derived boost or rotation data."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Lorentz Projection Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Projection formula: `{payload['projection_formula']}`",
        f"Symmetric formula: `{payload['symmetric_formula']}`",
        f"Linear Lorentz condition: `{payload['lorentz_condition_linear']}`",
        f"Scalar weak-field Lorentz generator zero: {payload['scalar_weakfield_lorentz_generator_zero']}",
        f"Symmetric stretch rejected as Q_cross: {payload['symmetric_stretch_rejected_as_qcross']}",
        f"Comoving scalar same-L identity conditionally selected: "
        f"{payload['comoving_scalar_same_l_identity_conditionally_selected']}",
        f"Non-comoving boost source required: {payload['noncomoving_boost_source_required']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Consequences",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["derived_consequences"])
    lines.extend(
        [
            "",
            f"Allowed branch: {payload['allowed_branch']}",
            "",
            f"Open branch: {payload['open_branch']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
