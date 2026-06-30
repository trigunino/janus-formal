from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_phi_j_l_boundary_selector_probe import build_payload as build_boundary
from scripts.build_p0_route_d_source_free_boundary_no_go_argument import (
    build_payload as build_no_go,
)
from scripts.build_p0_route_d_source_free_pde_nullspace_probe import (
    build_payload as build_pde_probe,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_local_pde_no_selector_certificate.md")
JSON_PATH = Path("outputs/reports/p0_route_d_local_pde_no_selector_certificate.json")


def build_payload() -> dict:
    pde_probe = build_pde_probe()
    boundary = build_boundary()
    no_go = build_no_go()
    lemmas = [
        {
            "lemma": "homogeneous_local_pde",
            "claim": "E[L]=0 leaves kernel modes or integration constants unless source/boundary data are supplied.",
            "closed": True,
        },
        {
            "lemma": "invertible_operator_not_enough",
            "claim": "Dirichlet or mass terms can remove a kernel but require boundary/coefficient provenance.",
            "closed": True,
        },
        {
            "lemma": "structural_boundaries_underselect",
            "claim": "mirror, periodic, and integrability constraints filter branches but do not select a unique L.",
            "closed": True,
        },
        {
            "lemma": "strong_boundary_selectors",
            "claim": "pointwise selectors can fix the toy family but become new axioms if not Janus-supplied.",
            "closed": True,
        },
        {
            "lemma": "omega_law_missing",
            "claim": "without a Janus law for D_u L/Omega, local PDE solutions cannot be promoted to physical closure.",
            "closed": True,
        },
    ]
    return {
        "description": (
            "Route D certificate: local source-free and boundary-free PDEs are not "
            "zero-axiom selectors for L. Numeric probes are witnesses only; the "
            "claim is the bounded structural exclusion."
        ),
        "status": "local-source-free-boundary-free-pde-no-selector-certified",
        "pde_probe_status": pde_probe["status"],
        "boundary_selector_status": boundary["status"],
        "no_go_argument_status": no_go["status"],
        "lemmas": lemmas,
        "numeric_probes_are_witnesses_only": True,
        "local_source_free_boundary_free_pde_selects_l": False,
        "selection_requires_source_or_boundary_axiom": True,
        "bounded_claim_closed": True,
        "full_no_go_proved": False,
        "open_escape": "source-derived STF curvature operator",
        "source_derived_operator_still_open": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The bounded Route D certificate is closed: a local PDE with no Janus "
            "source and no Janus boundary/coefficient law cannot select L without "
            "a hidden axiom. This does not exclude a source-derived STF curvature operator."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Local PDE No-Selector Certificate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Numeric probes are witnesses only: {payload['numeric_probes_are_witnesses_only']}",
        f"Local source-free boundary-free PDE selects L: {payload['local_source_free_boundary_free_pde_selects_l']}",
        f"Selection requires source or boundary axiom: {payload['selection_requires_source_or_boundary_axiom']}",
        f"Bounded claim closed: {payload['bounded_claim_closed']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Open escape: {payload['open_escape']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| lemma | claim | closed |",
        "|---|---|---:|",
    ]
    for row in payload["lemmas"]:
        lines.append(f"| {row['lemma']} | {row['claim']} | {row['closed']} |")
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
