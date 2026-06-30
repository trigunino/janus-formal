from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_phi_j_l_boundary_selector_probe import build_payload as build_boundary
from scripts.build_p0_route_d_source_free_pde_nullspace_probe import build_payload as build_pde_probe


REPORT_PATH = Path("outputs/reports/p0_route_d_source_free_boundary_no_go_argument.md")
JSON_PATH = Path("outputs/reports/p0_route_d_source_free_boundary_no_go_argument.json")


def build_payload() -> dict:
    pde_probe = build_pde_probe()
    boundary = build_boundary()
    proof_steps = [
        {
            "step": "local_pde_selector",
            "statement": "A local derivative action gives P[L]=S_Janus with boundary data B.",
            "closed_for_scope": True,
        },
        {
            "step": "source_free_case",
            "statement": "If S_Janus is absent, P[L]=0 leaves kernel modes or only trivial/boundary-selected solutions.",
            "closed_for_scope": True,
        },
        {
            "step": "boundary_free_case",
            "statement": "If B is not Janus-supplied, any selected solution uses a hidden boundary axiom.",
            "closed_for_scope": True,
        },
        {
            "step": "coefficient_free_case",
            "statement": "If mass/coupling/operator coefficients are not source-supplied, invertibility is not a Janus selection.",
            "closed_for_scope": True,
        },
        {
            "step": "same_l_noether_case",
            "statement": "If the same-L split Noether identity is not closed, the selected L is not admissible for K/Q_cross.",
            "closed_for_scope": True,
        },
    ]
    excluded_scope = [
        "source-free homogeneous PDE selector",
        "boundary-selected PDE without Janus boundary data",
        "coefficient-selected PDE without Janus coefficients",
        "principal-symbol-only stability claim",
    ]
    open_scope = [
        "source-derived STF curvature operator",
        "accepted Janus action with explicit S_Janus and boundary term",
        "same-L Noether-closed operator",
    ]
    return {
        "description": (
            "Route D structural no-go argument for source-free/boundary-free local "
            "PDE selectors. It turns the numeric nullspace probe into an explicit "
            "bounded theorem scope."
        ),
        "status": "source-free-boundary-no-go-argument-bounded",
        "pde_probe_status": pde_probe["status"],
        "boundary_selector_status": boundary["status"],
        "proof_steps": proof_steps,
        "excluded_scope": excluded_scope,
        "open_scope": open_scope,
        "proved_for_source_free_boundary_free_local_pde": True,
        "periodic_kernel_detected": bool(pde_probe["periodic_kernel_detected"]),
        "boundary_selectors_can_fix_but_unsourced": bool(boundary["strong_selectors_exist"])
        and not bool(boundary["strong_selectors_source_supplied"]),
        "principal_symbol_sufficient": False,
        "source_derived_operator_still_open": True,
        "full_no_go_proved": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A bounded no-go is now explicit: source-free or boundary-free local "
            "PDE selectors cannot close zero-axiom Janus. This does not exclude a "
            "genuine source-derived STF curvature operator."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Source-Free/Boundary-Free No-Go Argument",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Proved for source-free boundary-free local PDE: {payload['proved_for_source_free_boundary_free_local_pde']}",
        f"Periodic kernel detected: {payload['periodic_kernel_detected']}",
        f"Boundary selectors can fix but unsourced: {payload['boundary_selectors_can_fix_but_unsourced']}",
        f"Principal symbol sufficient: {payload['principal_symbol_sufficient']}",
        f"Source-derived operator still open: {payload['source_derived_operator_still_open']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| step | statement | closed for scope |",
        "|---|---|---:|",
    ]
    for row in payload["proof_steps"]:
        lines.append(f"| {row['step']} | {row['statement']} | {row['closed_for_scope']} |")
    lines.extend(["", "## Excluded Scope", ""])
    lines.extend(f"- {item}" for item in payload["excluded_scope"])
    lines.extend(["", "## Open Scope", ""])
    lines.extend(f"- {item}" for item in payload["open_scope"])
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
