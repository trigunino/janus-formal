from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_scalar_density_completion_gate import (
    build_payload as build_scalar_density,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_invariant_filter.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_invariant_filter.json")


def build_payload() -> dict:
    scalar_density = build_scalar_density()
    invariant_rows = [
        {
            "candidate": "curvature_difference_scalar",
            "form": "I_R = R_plus - PT^*R_minus",
            "diagonal_scalar": True,
            "pt_mirror_compatible": True,
            "same_l_required": False,
            "uses_fit": False,
            "survives_filter": True,
            "selects_coefficients": False,
            "blocker": "Janus source does not fix coefficient or nonlinear function of I_R",
        },
        {
            "candidate": "relative_metric_strain_trace",
            "form": "I_H = tr(g_plus^{-1} phi^*g_minus)-4",
            "diagonal_scalar": True,
            "pt_mirror_compatible": True,
            "same_l_required": True,
            "uses_fit": False,
            "survives_filter": True,
            "selects_coefficients": False,
            "blocker": "depends on source-selected phi/L, still open",
        },
        {
            "candidate": "matter_cross_trace",
            "form": "I_T = tr(T_plus L T_minus L^T)",
            "diagonal_scalar": True,
            "pt_mirror_compatible": True,
            "same_l_required": True,
            "uses_fit": False,
            "survives_filter": True,
            "selects_coefficients": False,
            "blocker": "pressure/Pi tensor transport is not closed",
        },
        {
            "candidate": "holonomy_trace",
            "form": "I_Omega = tr(P exp integral Omega)",
            "diagonal_scalar": True,
            "pt_mirror_compatible": True,
            "same_l_required": True,
            "uses_fit": False,
            "survives_filter": True,
            "selects_coefficients": False,
            "blocker": "path dependence filters branches but does not select the path law",
        },
        {
            "candidate": "pt_boundary_distance",
            "form": "I_B = signed distance to PT fixed surface",
            "diagonal_scalar": True,
            "pt_mirror_compatible": True,
            "same_l_required": False,
            "uses_fit": False,
            "survives_filter": True,
            "selects_coefficients": False,
            "blocker": "PT boundary/surface law is not source-derived",
        },
        {
            "candidate": "observable_residual",
            "form": "I_obs = lensing_or_growth_residual",
            "diagonal_scalar": False,
            "pt_mirror_compatible": False,
            "same_l_required": False,
            "uses_fit": True,
            "survives_filter": False,
            "selects_coefficients": False,
            "blocker": "observational fit is forbidden for C_J/V_J selection",
        },
    ]
    admissible = [row["candidate"] for row in invariant_rows if row["survives_filter"]]
    rejected = [row["candidate"] for row in invariant_rows if not row["survives_filter"]]
    return {
        "description": (
            "Admissibility filter for the C_J and V_J ingredients of S_path. "
            "It narrows the invariant basis without choosing coefficients by hand."
        ),
        "status": "spath-cj-vj-invariant-filter-underselects",
        "depends_on": ["p0_route_c_spath_scalar_density_completion_gate"],
        "scalar_density_contract_written": bool(scalar_density["scalar_density_contract_written"]),
        "invariant_rows": invariant_rows,
        "admissible_invariants": admissible,
        "rejected_invariants": rejected,
        "candidate_family": "C_J=c0+sum_i c_i I_i; V_J=sum_i v_i I_i+sum_ij v_ij I_i I_j",
        "filter_criteria": [
            "diagonal diffeomorphism scalar",
            "PT/mirror parity compatible",
            "same-L compatible when L appears",
            "no observational residual or fitted amplitude",
            "must pass later stability sign conditions C_0>0 and V_2>=0",
            "must have Janus source provenance before prediction",
        ],
        "admissible_invariant_count": len(admissible),
        "rejected_invariant_count": len(rejected),
        "all_survivors_underselect": True,
        "source_coefficients_fixed": False,
        "unique_cj_vj_selector_found": False,
        "stability_signs_fixed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The filter rejects fitted observables and keeps only covariant Janus "
            "invariant families. It still underselects C_J/V_J because no source "
            "fixes coefficients, nonlinear dependence, path branch, or stability signs."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path C_J/V_J Invariant Filter",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scalar density contract written: {payload['scalar_density_contract_written']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"Admissible invariant count: {payload['admissible_invariant_count']}",
        f"Rejected invariant count: {payload['rejected_invariant_count']}",
        f"All survivors underselect: {payload['all_survivors_underselect']}",
        f"Source coefficients fixed: {payload['source_coefficients_fixed']}",
        f"Unique C_J/V_J selector found: {payload['unique_cj_vj_selector_found']}",
        f"Stability signs fixed: {payload['stability_signs_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| candidate | form | scalar | PT/mirror | same-L required | uses fit | survives | blocker |",
        "|---|---|---:|---:|---:|---:|---:|---|",
    ]
    for row in payload["invariant_rows"]:
        lines.append(
            f"| {row['candidate']} | `{row['form']}` | {row['diagonal_scalar']} | "
            f"{row['pt_mirror_compatible']} | {row['same_l_required']} | "
            f"{row['uses_fit']} | {row['survives_filter']} | {row['blocker']} |"
        )
    lines.extend(["", "## Filter Criteria", ""])
    lines.extend(f"- {item}" for item in payload["filter_criteria"])
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
