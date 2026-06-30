from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_local_low_derivative_scalar_tensor_no_go_expansion import (
    build_payload as build_expansion,
)
from scripts.build_p0_local_phi_scouple_no_go_target import build_payload as build_target
from scripts.build_p0_route_d_derivative_curvature_nullspace_gate import (
    build_payload as build_nullspace,
)
from scripts.build_p0_route_d_tensor_derivative_admissibility_filter import (
    build_payload as build_admissibility,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_no_go_structural_matrix.md")
JSON_PATH = Path("outputs/reports/p0_route_d_no_go_structural_matrix.json")


def build_payload() -> dict:
    expansion = build_expansion()
    target = build_target()
    nullspace = build_nullspace()
    admissibility = build_admissibility()
    matrix_rows = [
        {
            "family": "pure_pullback",
            "el_operator": "zero/on-shell Noether",
            "split_noether_rank": "insufficient",
            "same_l": "not selected",
            "stability": "not applicable",
            "excluded": True,
        },
        {
            "family": "ultralocal_scalar",
            "el_operator": "algebraic",
            "split_noether_rank": "rank deficient",
            "same_l": "DL absent",
            "stability": "no dynamics",
            "excluded": True,
        },
        {
            "family": "matter_scalar",
            "el_operator": "dust only partial",
            "split_noether_rank": "pressure/Pi open",
            "same_l": "tensor transport absent",
            "stability": "EOS missing",
            "excluded": True,
        },
        {
            "family": "tracefree_tensor",
            "el_operator": "possible P_STF source",
            "split_noether_rank": "untested",
            "same_l": "same bridge required",
            "stability": "ghost gate required",
            "excluded": False,
        },
        {
            "family": "derivative_curvature",
            "el_operator": "possible differential source",
            "split_noether_rank": "untested",
            "same_l": "curvature/connection route required",
            "stability": "principal symbol required",
            "excluded": False,
        },
    ]
    excluded_count = sum(1 for row in matrix_rows if row["excluded"])
    return {
        "description": "Route D structural matrix for expanding the local scalar/tensor no-go theorem.",
        "status": "no-go-structural-matrix-open",
        "target_status": target["status"],
        "expansion_status": expansion["status"],
        "nullspace_status": nullspace["status"],
        "admissibility_filter_status": admissibility["status"],
        "matrix_rows": matrix_rows,
        "excluded_family_count": excluded_count,
        "open_family_count": len(matrix_rows) - excluded_count,
        "restricted_no_go_proved": bool(expansion["restricted_scalar_no_go_proved"]),
        "full_no_go_proved": False,
        "accepted_candidate_exists": False,
        "free_tensor_routes_excluded": not bool(admissibility["free_tracefree_tensor_allowed"]),
        "source_free_derivative_subfamily_excluded": bool(nullspace["homogeneous_source_free_subfamily_excluded"]),
        "source_derived_stf_operator_open": bool(nullspace["source_derived_stf_curvature_operator_open"]),
        "requires_janus_provenance": True,
        "requires_ghost_stability": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The matrix turns Route D into a structural proof program: easy scalar families "
            "are excluded, while trace-free tensor and derivative/curvature families remain "
            "open until Janus provenance and stability tests close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D No-Go Structural Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target status: {payload['target_status']}",
        f"Expansion status: {payload['expansion_status']}",
        f"Nullspace status: {payload['nullspace_status']}",
        f"Admissibility filter status: {payload['admissibility_filter_status']}",
        f"Excluded family count: {payload['excluded_family_count']}",
        f"Open family count: {payload['open_family_count']}",
        f"Restricted no-go proved: {payload['restricted_no_go_proved']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Accepted candidate exists: {payload['accepted_candidate_exists']}",
        f"Free tensor routes excluded: {payload['free_tensor_routes_excluded']}",
        f"Source-free derivative subfamily excluded: {payload['source_free_derivative_subfamily_excluded']}",
        f"Source-derived STF operator open: {payload['source_derived_stf_operator_open']}",
        f"Requires Janus provenance: {payload['requires_janus_provenance']}",
        f"Requires ghost/stability: {payload['requires_ghost_stability']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| family | EL operator | split Noether rank | same-L | stability | excluded |",
        "|---|---|---|---|---|---:|",
    ]
    for row in payload["matrix_rows"]:
        lines.append(
            f"| {row['family']} | {row['el_operator']} | {row['split_noether_rank']} | "
            f"{row['same_l']} | {row['stability']} | {row['excluded']} |"
        )
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
