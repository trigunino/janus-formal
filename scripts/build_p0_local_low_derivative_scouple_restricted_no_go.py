from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_b4vol_jacobian_gauge_degeneracy_proof import (
    build_payload as build_b4vol_degeneracy,
)
from scripts.build_p0_matter_pullback_action_deep_audit import (
    build_payload as build_matter_pullback,
)
from scripts.build_p0_noether_split_rank_obstruction import build_payload as build_noether
from scripts.build_p0_scouple_internal_variational_candidate_solver import (
    build_payload as build_metric_invariant,
)
from scripts.build_p0_scouple_matter_invariant_solver import (
    build_payload as build_matter_invariant,
)


REPORT_PATH = Path("outputs/reports/p0_local_low_derivative_scouple_restricted_no_go.md")
JSON_PATH = Path("outputs/reports/p0_local_low_derivative_scouple_restricted_no_go.json")


def build_payload() -> dict:
    pullback = build_matter_pullback()
    metric = build_metric_invariant()
    matter = build_matter_invariant()
    noether = build_noether()
    b4vol = build_b4vol_degeneracy()

    obstruction_rows = [
        {
            "obstruction": "pure_pullback_identity",
            "evidence": "pure matter pullback has zero phi Euler-Lagrange operator",
            "closed": bool(pullback["pure_pullback_euler_lagrange_zero"]),
            "blocks": "passive pullback cannot select phi/J/L",
        },
        {
            "obstruction": "b4vol_product_degeneracy",
            "evidence": "B4vol=J_phi*S_slice is invariant under compensating rescaling",
            "closed": bool(b4vol["degeneracy_symbolic_identity_closed"]),
            "blocks": "source B4vol alone cannot isolate J_phi",
        },
        {
            "obstruction": "ultralocal_metric_invariant_family",
            "evidence": "basic stationarity fixes c0,c1 but leaves c2,c3 free",
            "closed": bool(
                metric["aligned_branch_stationary"]
                and metric["zero_vacuum_energy_fixed"]
                and not metric["unique_phi_forced"]
            ),
            "blocks": "local Phi(I_metric) is not unique",
        },
        {
            "obstruction": "no_l_transport_from_ultralocal_l",
            "evidence": "delta S/delta L is algebraic, not a D L transport law",
            "closed": bool(not metric["el_is_transport_equation"]),
            "blocks": "same-L/DL/Q_cross transport is not derived",
        },
        {
            "obstruction": "matter_scalar_family_open",
            "evidence": "dust coefficient fixed, pressure/Pi coefficients remain source-free",
            "closed": bool(
                matter["dust_coefficient_fixed"]
                and not matter["pressure_coefficient_source_fixed"]
                and not matter["pi_coefficient_source_fixed"]
            ),
            "blocks": "general matter closure without EOS/Pi law",
        },
        {
            "obstruction": "single_noether_rank_one",
            "evidence": "single diagonal Noether identity has rank 1",
            "closed": bool(noether["diagonal_identity_rank"] == 1),
            "blocks": "cannot force both R_plus=0 and R_minus=0",
        },
    ]
    restricted_class = [
        "pure pulled matter top-form terms",
        "ultralocal scalar metric invariants Phi(I_metric) with no D L terms",
        "linear scalar matter invariant a*rho+b*p+c*Pi",
        "M15-style B4vol product anchoring without independent lapse/slice selector",
        "one diagonal diffeomorphism Noether identity",
    ]
    exclusions = [
        "higher-derivative terms such as D L D L or curvature-dependent couplings",
        "nonlocal/history kernels",
        "independent sector diffeomorphism identities from a restored two-gauge action",
        "source-derived actions, including Hamiltonian/phase-space branches outside scalar invariant class",
        "published Janus action term not represented by the restricted ansatz",
    ]
    restricted_no_go_proved = all(row["closed"] for row in obstruction_rows)
    return {
        "description": "Restricted no-go proof for easy local low-derivative S_couple closures.",
        "status": "restricted-local-low-derivative-scouple-no-go-proved",
        "restricted_class": restricted_class,
        "exclusions": exclusions,
        "obstruction_rows": obstruction_rows,
        "restricted_no_go_proved": restricted_no_go_proved,
        "full_local_low_derivative_no_go_proved": False,
        "pure_pullback_selects_phi_j_l": bool(pullback["pure_matter_pullback_selects_phi_j_l"]),
        "metric_invariant_unique_phi_forced": bool(metric["unique_phi_forced"]),
        "metric_invariant_el_is_transport": bool(metric["el_is_transport_equation"]),
        "matter_invariant_unique": bool(matter["matter_family_unique"]),
        "split_noether_closes_two_residuals": bool(
            noether["single_identity_can_force_both_residuals_zero"]
        ),
        "b4vol_alone_selects_jphi": bool(b4vol["source_b4vol_alone_selects_jphi"]),
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The restricted easy class is eliminated: pure pullback, ultralocal "
            "metric/matter scalar invariants, B4vol product anchoring, and one "
            "diagonal Noether identity cannot select phi/J/L or close both residuals. "
            "This is not a full no-go theorem for higher-derivative, nonlocal, or "
            "source-derived actions outside the class."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Local Low-Derivative S_couple Restricted No-Go",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Restricted no-go proved: {payload['restricted_no_go_proved']}",
        f"Full local low-derivative no-go proved: {payload['full_local_low_derivative_no_go_proved']}",
        f"Pure pullback selects phi/J/L: {payload['pure_pullback_selects_phi_j_l']}",
        f"Metric invariant unique phi forced: {payload['metric_invariant_unique_phi_forced']}",
        f"Metric invariant EL is transport: {payload['metric_invariant_el_is_transport']}",
        f"Matter invariant unique: {payload['matter_invariant_unique']}",
        f"Split Noether closes two residuals: {payload['split_noether_closes_two_residuals']}",
        f"B4vol alone selects J_phi: {payload['b4vol_alone_selects_jphi']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Restricted Class",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["restricted_class"])
    lines.extend(
        [
            "",
            "## Obstruction Rows",
            "",
            "| obstruction | evidence | closed | blocks |",
            "|---|---|---:|---|",
        ]
    )
    for row in payload["obstruction_rows"]:
        lines.append(
            f"| {row['obstruction']} | {row['evidence']} | {row['closed']} | {row['blocks']} |"
        )
    lines.extend(["", "## Exclusions", ""])
    lines.extend(f"- {item}" for item in payload["exclusions"])
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
