from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_flrw_dust_transport_branch.md")
JSON_PATH = Path("outputs/reports/bianchi_flrw_dust_transport_branch.json")


def build_payload() -> dict:
    notation = {
        "det4_metric_plus": "former B_plus; metric determinant factor in the positive equation",
        "det4_metric_minus": "former B_minus; metric determinant factor in the negative equation",
        "transport3_dust_plus": "former F_plus; scalar transport factor needed by dust continuity",
        "transport3_dust_minus": "former F_minus; scalar transport factor needed by dust continuity",
        "weight3_dust_plus": "det4_metric_plus transport3_dust_plus",
        "weight3_dust_minus": "det4_metric_minus transport3_dust_minus",
    }
    assumptions = [
        "homogeneous FLRW branch",
        "common time coordinate",
        "dust only: p_plus=p_minus=0",
        "rho_plus obeys dot(rho_plus)+3 H_plus rho_plus=0",
        "rho_minus obeys dot(rho_minus)+3 H_minus rho_minus=0",
        "cross term is scalar-density transport only, not full tensor transport",
    ]
    positive_branch = {
        "cross_source": "X_plus = det4_metric_plus transport3_dust_plus rho_minus",
        "closure_equation": "dot(X_plus)+3 H_plus X_plus = 0",
        "transport_condition": (
            "d_t ln(transport3_dust_plus)=3(H_minus-H_plus)-d_t ln(det4_metric_plus)"
        ),
        "power_law_case": "if det4_metric_plus=(a_minus/a_plus)^n_det_plus",
        "transport_factor": (
            "transport3_dust_plus proportional "
            "(a_minus/a_plus)^(3-n_det_plus)"
        ),
        "combined_weight": "weight3_dust_plus proportional (a_minus/a_plus)^3",
    }
    negative_branch = {
        "cross_source": "X_minus = det4_metric_minus transport3_dust_minus rho_plus",
        "closure_equation": "dot(X_minus)+3 H_minus X_minus = 0",
        "transport_condition": (
            "d_t ln(transport3_dust_minus)=3(H_plus-H_minus)-d_t ln(det4_metric_minus)"
        ),
        "power_law_case": "if det4_metric_minus=(a_plus/a_minus)^n_det_minus",
        "transport_factor": (
            "transport3_dust_minus proportional "
            "(a_plus/a_minus)^(3-n_det_minus)"
        ),
        "combined_weight": "weight3_dust_minus proportional (a_plus/a_minus)^3",
    }
    non_claims = [
        "does not derive generic K_plus/K_minus tensors",
        "does not include pressure or anisotropic stress",
        "does not derive Q_cross",
        "does not turn a_minus/a_plus into a lensing amplitude",
        "does not close survey-level tensor lensing",
    ]
    notation_guards = [
        "det4_metric_* is the determinant factor; transport3_dust_* is the additional scalar transport factor",
        "if det4_metric_plus=(a_minus/a_plus)^4 then transport3_dust_plus proportional (a_minus/a_plus)^-1",
        "the combined weight3_dust_* branch remains cubic, not quartic",
        "rho_minus proper, |rho_minus|, and positive-effective density must not be mixed",
        "do not multiply a positive-effective density by det4_metric_plus again",
    ]
    return {
        "description": "Special FLRW dust branch for Bianchi-compatible scalar density transport.",
        "status": "special-branch-derivation",
        "branch_closed": True,
        "physics_closed": False,
        "notation": notation,
        "assumptions": assumptions,
        "positive_branch": positive_branch,
        "negative_branch": negative_branch,
        "non_claims": non_claims,
        "notation_guards": notation_guards,
        "verdict": (
            "For homogeneous dust, the scalar transported cross-density must carry "
            "the volume ratio cubed after determinant and transport factors are "
            "combined. This is a branch result, not the missing generic tensor map."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi FLRW Dust Transport Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch closed: {payload['branch_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
    ]
    lines.extend(["## Notation", ""])
    for name, value in payload["notation"].items():
        lines.append(f"- `{name}`: {value}")
    lines.extend(["", "## Assumptions", ""])
    lines.extend(f"- {item}" for item in payload["assumptions"])
    for title, key in (
        ("Positive Branch", "positive_branch"),
        ("Negative Branch", "negative_branch"),
    ):
        lines.extend(["", f"## {title}", ""])
        for name, value in payload[key].items():
            lines.append(f"- {name}: `{value}`")
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in payload["non_claims"])
    lines.extend(["", "## Notation Guards", ""])
    lines.extend(f"- {item}" for item in payload["notation_guards"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
