from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_identity_obstruction_bifurcation.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_identity_obstruction_bifurcation.json")


def build_payload() -> dict:
    obstruction = {
        "standard_sources": "bulk flux + spinor boundary term + Nieh-Yan + Cartan-GHY",
        "identity_residue": "m_I = 4*q_T*Delta_chi",
        "standard_invariant_channels": "Nieh-Yan cancels C; Cartan-GHY can generate G; neither contributes -I",
        "no_go_condition": "for q_T != 0 and Delta_chi != 0, standard sources cannot set m_I=0",
    }
    eft_branch = {
        "counterterm": "M_EFT = m_EFT*I",
        "exact_value": "m_EFT = -4*q_T*Delta_chi",
        "effect": "cancels identity residue algebraically",
        "cost": "new boundary EFT parameter unless derived from a Janus volume invariant",
        "prediction_ready": False,
    }
    theorem_status = {
        "identity_obstruction_recorded": True,
        "standard_sources_no_go_if_qT_and_delta_nonzero": True,
        "eft_counterterm_closes_identity_channel": True,
        "eft_counterterm_source_derived_from_janus": False,
        "pure_geometric_closure_available": False,
        "prediction_ready": False,
    }
    obligations = [
        "either derive M_EFT from a Janus volume/determinant boundary invariant",
        "or record final no-go for pure geometric Dirac-Cartan boundary closure",
        "if EFT is accepted, propagate explicit non-geometric boundary parameter through stability reports",
    ]
    return {
        "description": "Identity-channel obstruction and EFT bifurcation for Janus boundary RUN 1.",
        "status": "pure-geometric-no-go-or-explicit-eft-branch",
        "obstruction": obstruction,
        "eft_branch": eft_branch,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Standard geometric surface invariants cannot cancel the trace identity residue. "
            "An EFT scalar boundary counterterm can close the algebra, but only as an explicit "
            "extension unless a Janus volume invariant derives it."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Identity Obstruction Bifurcation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Obstruction",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["obstruction"].items())
    lines.extend(["", "## EFT Branch"])
    lines.extend(f"- {key}: {value}" for key, value in payload["eft_branch"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
