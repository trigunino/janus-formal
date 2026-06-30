from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_nieh_yan_anomaly_derivation import build_payload as build_eta_payload
from scripts.build_p0_eft_orbifold_holonomy_quantization import build_payload as build_sigma_payload
from scripts.build_p0_eft_global_topology_closure_requirements import (
    build_payload as build_topology_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_holst_geometric_lock.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_geometric_lock.json")


def build_payload() -> dict:
    eta_payload = build_eta_payload()
    sigma_payload = build_sigma_payload()
    topology_payload = build_topology_payload()
    locks = {
        "eta_H_observed": -2.0,
        "eta_H_candidate_origin": "integer Holst/Nieh-Yan chiral trace of the boundary spin connection",
        "eta_H_required_identity": "eta_H + 2 = 0",
        "eta_H_local_trace_identity_residual": eta_payload["derivation"][
            "identity_residual_eta_H_plus_2"
        ],
        "a_sigma_observed": "2/3",
        "z_sigma_observed": "1/2",
        "a_sigma_candidate_origin": "Z2 de Sitter orbifold holonomy volume quantum",
        "a_sigma_required_identity": "3*a_sigma - 2 = 0",
        "a_sigma_local_holonomy_identity_residual": sigma_payload["derivation"][
            "identity_residual_3a_sigma_minus_2"
        ],
    }
    theorem_status = {
        "holst_branch_observationally_accepted": True,
        "eta_H_integer_lock_candidate_encoded": True,
        "a_sigma_rational_lock_candidate_encoded": True,
        "eta_H_local_trace_identity_closed": eta_payload["theorem_status"][
            "eta_H_plus_2_identity_closed_under_standard_trace_normalization"
        ],
        "a_sigma_local_holonomy_identity_closed": sigma_payload["theorem_status"][
            "a_sigma_identity_closed_under_holonomy_volume_quantum"
        ],
        "eta_H_derived_from_Holst_Nieh_Yan_trace": False,
        "a_sigma_derived_from_orbifold_holonomy": False,
        "aps_global_normalization_closed": topology_payload["theorem_status"][
            "aps_global_normalization_closed"
        ],
        "orbifold_global_cover_closed": topology_payload["theorem_status"][
            "orbifold_global_cover_closed"
        ],
        "full_cosmology_prediction_ready_conditionally": True,
        "full_cosmology_prediction_ready_no_fit": False,
    }
    obligations = [
        "compute the Holst/Nieh-Yan boundary trace and prove eta_H+2=0",
        "compute the de Sitter orbifold holonomy volume condition and prove 3*a_sigma-2=0",
        "only then promote the Holst branch from fitted/selected to no-fit geometric",
    ]
    global_requirements = topology_payload["global_requirements"]
    return {
        "description": "Geometric lock audit for the accepted Holst/membrane branch.",
        "status": "observational-lock-found-geometric-proof-open",
        "locks": locks,
        "theorem_status": theorem_status,
        "global_requirements": global_requirements,
        "obligations": obligations,
        "verdict": (
            "The accepted branch is statistically strong, but eta_H=-2 and a_sigma=2/3 "
            "remain grid-selected until the Holst trace and orbifold holonomy identities "
            "are derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Geometric Lock",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Locks",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["locks"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Global Requirements"])
    for key, item in payload["global_requirements"].items():
        lines.extend(
            [
                f"- {key}",
                f"  - needed_statement: {item['needed_statement']}",
                f"  - current_status: {item['current_status']}",
            ]
        )
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
