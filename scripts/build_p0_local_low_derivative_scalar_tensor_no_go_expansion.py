from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_local_low_derivative_scouple_restricted_no_go import (
    build_payload as build_restricted_no_go,
)
from scripts.build_p0_h_strain_ghost_symbolic_gate import build_payload as build_ghost
from scripts.build_p0_tracefree_h_source_action_provenance_chain_gate import (
    build_payload as build_tf_provenance,
)


REPORT_PATH = Path("outputs/reports/p0_local_low_derivative_scalar_tensor_no_go_expansion.md")
JSON_PATH = Path("outputs/reports/p0_local_low_derivative_scalar_tensor_no_go_expansion.json")


def build_payload() -> dict:
    restricted = build_restricted_no_go()
    ghost = build_ghost()
    tf = build_tf_provenance()
    family_rows = [
        {"family": "ultralocal_scalar", "excluded": bool(restricted["restricted_no_go_proved"]), "survives_as": None},
        {"family": "tracefree_tensor_H_TF", "excluded": False, "survives_as": "needs source provenance and stability"},
        {"family": "derivative_strain", "excluded": False, "survives_as": "only if ghost/stability and source action pass"},
        {"family": "curvature_dependent", "excluded": False, "survives_as": "outside restricted low-derivative scalar class"},
        {"family": "nonlocal_kernel", "excluded": False, "survives_as": "outside local theorem"},
    ]
    return {
        "description": "Route D expansion from restricted scalar no-go toward scalar/tensor local theorem.",
        "status": "scalar-tensor-no-go-expanded-full-theorem-open",
        "family_rows": family_rows,
        "restricted_scalar_no_go_proved": bool(restricted["restricted_no_go_proved"]),
        "tracefree_source_provenance_closed": bool(tf["source_action_provenance_closed"]),
        "ghost_gate_available": True,
        "source_derived_action_missing": bool(ghost["source_derived_action_missing"]),
        "accepted_candidate_exists": False,
        "full_local_low_derivative_theorem_proved": False,
        "surviving_families": ["tracefree_tensor_H_TF", "derivative_strain", "curvature_dependent", "nonlocal_kernel"],
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The easy scalar class is excluded, but the full scalar/tensor no-go theorem is "
            "not proved. Surviving families must pass Janus provenance plus ghost/stability gates."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Local Low-Derivative Scalar/Tensor No-Go Expansion",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Restricted scalar no-go proved: {payload['restricted_scalar_no_go_proved']}",
        f"Tracefree source provenance closed: {payload['tracefree_source_provenance_closed']}",
        f"Ghost gate available: {payload['ghost_gate_available']}",
        f"Source-derived action missing: {payload['source_derived_action_missing']}",
        f"Accepted candidate exists: {payload['accepted_candidate_exists']}",
        f"Full local low-derivative theorem proved: {payload['full_local_low_derivative_theorem_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| family | excluded | survives as |",
        "|---|---:|---|",
    ]
    for row in payload["family_rows"]:
        lines.append(f"| {row['family']} | {row['excluded']} | {row['survives_as']} |")
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
