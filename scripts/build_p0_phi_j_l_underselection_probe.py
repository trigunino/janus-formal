from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_phi_j_l_boundary_selector_probe import (
    build_payload as build_boundary_selector,
)
from scripts.build_p0_phi_j_l_intrinsic_selector_attempt import (
    build_payload as build_intrinsic_selector,
)
from scripts.build_p0_janus_equations_to_phi_selector_probe import (
    build_payload as build_janus_selector,
)


REPORT_PATH = Path("outputs/reports/p0_phi_j_l_underselection_probe.md")
JSON_PATH = Path("outputs/reports/p0_phi_j_l_underselection_probe.json")


def _candidate(epsilon: float, n: int = 256) -> dict:
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    phi = x + epsilon * np.sin(x)
    jacobian = 1.0 + epsilon * np.cos(x)
    b4vol = jacobian
    l_map = jacobian
    dl = -epsilon * np.sin(x)
    return {
        "epsilon": epsilon,
        "min_jacobian": float(np.min(jacobian)),
        "max_jacobian": float(np.max(jacobian)),
        "invertible": bool(np.min(jacobian) > 0.0),
        "b4vol_equals_jacobian": bool(np.allclose(b4vol, jacobian)),
        "dl_equals_dj": bool(np.allclose(dl, -epsilon * np.sin(x))),
        "sample_phi": [float(phi[0]), float(phi[n // 4]), float(phi[n // 2])],
    }


def build_payload() -> dict:
    boundary = build_boundary_selector()
    intrinsic = build_intrinsic_selector()
    janus_selector = build_janus_selector()
    candidates = [_candidate(eps) for eps in [0.0, 0.05, -0.05, 0.1]]
    jacobian_ranges = {(row["min_jacobian"], row["max_jacobian"]) for row in candidates}
    admissible = all(
        row["invertible"] and row["b4vol_equals_jacobian"] and row["dl_equals_dj"]
        for row in candidates
    )
    distinct = len(jacobian_ranges) > 1
    local_tests = [
        {
            "test": "integrability",
            "result": "1D maps phi=x+epsilon sin(x) have J=dphi and no curl obstruction",
            "closed": admissible,
        },
        {
            "test": "b4vol_identity",
            "result": "with unit lapse/slice, B4vol=J for every epsilon",
            "closed": admissible,
        },
        {
            "test": "dl_identity",
            "result": "with unit tetrads, L=J and D L=D J for every epsilon",
            "closed": admissible,
        },
        {
            "test": "unique_selection",
            "result": "epsilon remains free without source or boundary data",
            "closed": False,
        },
    ]
    return {
        "description": "Underselection probe for Janus phi/J/L source selection after local identities close.",
        "status": "phi-j-l-underselection-open",
        "candidate_family": "phi_epsilon(x)=x+epsilon sin(x), |epsilon|<1",
        "candidates": candidates,
        "local_tests": local_tests,
        "all_candidates_locally_admissible": admissible,
        "distinct_admissible_maps_exist": distinct,
        "underselection_proved_for_family": bool(admissible and distinct),
        "boundary_selector_probe_status": boundary["status"],
        "strong_boundary_selectors_exist": boundary["strong_selectors_exist"],
        "strong_boundary_selectors_source_supplied": boundary["strong_selectors_source_supplied"],
        "mirror_topology_alone_fixes_unique_map": boundary["mirror_topology_alone_fixes_unique_map"],
        "intrinsic_selector_attempt_status": intrinsic["status"],
        "intrinsic_selector_fixes_toy_family": intrinsic["intrinsic_selector_fixes_toy_family"],
        "intrinsic_selector_source_derived": intrinsic["source_derived_from_janus"],
        "janus_equations_selector_status": janus_selector["status"],
        "janus_equations_select_b4vol_weight": janus_selector["janus_equations_select_b4vol_weight"],
        "janus_equations_select_phi_without_extra_gauge": janus_selector[
            "janus_equations_select_phi_without_extra_gauge"
        ],
        "source_boundary_conditions_supplied": False,
        "unique_phi_j_l_selected": False,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "remaining_selectors": [
            "Janus source action selecting epsilon or an equivalent map equation",
            "boundary/initial data from a published Janus branch",
            "topological or mirror regularity condition strong enough to fix the map",
            "explicit new axiom declared before observation comparison",
        ],
        "verdict": (
            "Local integrability, B4vol bookkeeping, and D L identities do not select a "
            "unique phi/J/L. A source or boundary principle is still required."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/J/L Underselection Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"All candidates locally admissible: {payload['all_candidates_locally_admissible']}",
        f"Distinct admissible maps exist: {payload['distinct_admissible_maps_exist']}",
        f"Underselection proved for family: {payload['underselection_proved_for_family']}",
        f"Boundary selector probe status: {payload['boundary_selector_probe_status']}",
        f"Strong boundary selectors exist: {payload['strong_boundary_selectors_exist']}",
        f"Strong boundary selectors source supplied: {payload['strong_boundary_selectors_source_supplied']}",
        f"Mirror/topology alone fixes unique map: {payload['mirror_topology_alone_fixes_unique_map']}",
        f"Intrinsic selector attempt status: {payload['intrinsic_selector_attempt_status']}",
        f"Intrinsic selector fixes toy family: {payload['intrinsic_selector_fixes_toy_family']}",
        f"Intrinsic selector source derived: {payload['intrinsic_selector_source_derived']}",
        f"Janus equations selector status: {payload['janus_equations_selector_status']}",
        f"Janus equations select B4vol weight: {payload['janus_equations_select_b4vol_weight']}",
        (
            "Janus equations select phi without extra gauge: "
            f"{payload['janus_equations_select_phi_without_extra_gauge']}"
        ),
        f"Source/boundary conditions supplied: {payload['source_boundary_conditions_supplied']}",
        f"Unique phi/J/L selected: {payload['unique_phi_j_l_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidates",
        "",
        "| epsilon | min J | max J | invertible |",
        "|---:|---:|---:|---:|",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"| {row['epsilon']} | {row['min_jacobian']:.6g} | "
            f"{row['max_jacobian']:.6g} | {row['invertible']} |"
        )
    lines.extend(["", "## Local Tests", "", "| test | result | closed |", "|---|---|---:|"])
    for row in payload["local_tests"]:
        lines.append(f"| {row['test']} | {row['result']} | {row['closed']} |")
    lines.extend(["", "## Remaining Selectors", ""])
    lines.extend(f"- {item}" for item in payload["remaining_selectors"])
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
