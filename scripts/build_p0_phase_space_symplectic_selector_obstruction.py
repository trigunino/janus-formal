from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_phase_space_symplectic_selector_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_phase_space_symplectic_selector_obstruction.json")


def _canonical_row(a: float) -> dict:
    phase_space_det = a * (1.0 / a)
    return {
        "a": a,
        "x_scale": a,
        "p_scale": 1.0 / a,
        "phase_space_determinant": phase_space_det,
        "liouville_preserved": math.isclose(phase_space_det, 1.0),
        "symplectic_form_preserved": math.isclose(phase_space_det, 1.0),
        "projected_j_phi_candidate": a,
    }


def build_payload() -> dict:
    family = [_canonical_row(a) for a in [0.25, 0.5, 1.0, 2.0, 4.0]]
    projected_j_values = {row["projected_j_phi_candidate"] for row in family}
    canonical_for_all = all(
        row["liouville_preserved"] and row["symplectic_form_preserved"] for row in family
    )
    return {
        "description": (
            "Bounded zero-rustine obstruction: canonical/Liouville preservation fixes the "
            "phase-space determinant, not the spacetime selector J_phi."
        ),
        "status": "phase-space-symplectic-selector-obstruction-open",
        "candidate_family": "x -> a x, p -> p/a with a>0",
        "family": family,
        "canonical_liouville_det_equals_one": canonical_for_all,
        "arbitrary_positive_a_allowed": True,
        "projected_j_phi_values_distinct": len(projected_j_values) > 1,
        "phase_space_route_selects_j_phi": False,
        "phase_space_route_closes_phi_j_l": False,
        "requires_hamiltonian_or_source_branch": True,
        "observational_fit_forbidden": True,
        "uses_observational_fit": False,
        "qdet_qcross_absorption_forbidden": True,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_forbidden": True,
        "hidden_axiom_adopted": False,
        "physics_closed": False,
        "prediction_ready": False,
        "bounded_scope": (
            "This artifact only blocks the phase-space/Liouville/symplectic route as a "
            "standalone selector; it does not reject a Hamiltonian or source-derived branch."
        ),
        "verdict": (
            "Canonical volume preservation gives det(dx,dp)=1, but the family x->a x, "
            "p->p/a remains canonical for every positive a. The projected spacetime "
            "J_phi is therefore not selected, so phi/J/L cannot close from the "
            "phase-space route alone."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phase-Space Symplectic Selector Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"Canonical/Liouville det equals one: {payload['canonical_liouville_det_equals_one']}",
        f"Arbitrary positive a allowed: {payload['arbitrary_positive_a_allowed']}",
        f"Projected J_phi values distinct: {payload['projected_j_phi_values_distinct']}",
        f"Phase-space route selects J_phi: {payload['phase_space_route_selects_j_phi']}",
        f"Phase-space route closes phi/J/L: {payload['phase_space_route_closes_phi_j_l']}",
        f"Requires Hamiltonian/source branch: {payload['requires_hamiltonian_or_source_branch']}",
        f"Observational fit forbidden: {payload['observational_fit_forbidden']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Q_det/Q_cross absorption forbidden: {payload['qdet_qcross_absorption_forbidden']}",
        f"Uses Q_det/Q_cross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom forbidden: {payload['hidden_axiom_forbidden']}",
        f"Hidden axiom adopted: {payload['hidden_axiom_adopted']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Canonical Family",
        "",
        "| a | x scale | p scale | det phase space | projected J_phi |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["family"]:
        lines.append(
            f"| {row['a']:.6g} | {row['x_scale']:.6g} | {row['p_scale']:.6g} | "
            f"{row['phase_space_determinant']:.6g} | {row['projected_j_phi_candidate']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"Bounded scope: {payload['bounded_scope']}",
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
