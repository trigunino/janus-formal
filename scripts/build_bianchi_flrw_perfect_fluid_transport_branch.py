from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_flrw_perfect_fluid_transport_branch.md")
JSON_PATH = Path("outputs/reports/bianchi_flrw_perfect_fluid_transport_branch.json")


def build_payload() -> dict:
    notation = {
        "det4_metric_plus": "former B_plus; metric determinant factor in the positive equation",
        "det4_metric_minus": "former B_minus; metric determinant factor in the negative equation",
        "transport_pf_plus": "former F_plus; scalar perfect-fluid transport factor",
        "transport_pf_minus": "former F_minus; scalar perfect-fluid transport factor",
        "weight_pf_plus": "det4_metric_plus transport_pf_plus",
        "weight_pf_minus": "det4_metric_minus transport_pf_minus",
    }
    assumptions = [
        "homogeneous FLRW branch",
        "common time coordinate",
        "barotropic perfect fluids with declared w_plus, w_minus",
        "rho_s obeys dot(rho_s)+3 H_s (1+w_s) rho_s=0",
        "cross source is scalar perfect-fluid transport, not anisotropic stress",
        "receiver-sector effective cross equation of state must be declared",
    ]
    positive_branch = {
        "cross_source": "X_plus = det4_metric_plus transport_pf_plus rho_minus",
        "receiver_closure": "dot(X_plus)+3 H_plus (1+w_cross_plus) X_plus=0",
        "transport_condition": (
            "d_t ln(transport_pf_plus)=3 H_minus(1+w_minus)"
            "-3 H_plus(1+w_cross_plus)-d_t ln(det4_metric_plus)"
        ),
        "constant_w_integral": (
            "transport_pf_plus proportional a_minus^(3(1+w_minus)) "
            "a_plus^(-3(1+w_cross_plus)) / det4_metric_plus"
        ),
        "power_law_b_case": (
            "if det4_metric_plus=(a_minus/a_plus)^n_det_plus, "
            "then transport_pf_plus proportional "
            "a_minus^(3(1+w_minus)-n_det_plus) "
            "a_plus^(-3(1+w_cross_plus)+n_det_plus)"
        ),
        "combined_weight": (
            "weight_pf_plus proportional a_minus^(3(1+w_minus)) "
            "a_plus^(-3(1+w_cross_plus))"
        ),
        "dust_limit": "w_minus=w_cross_plus=0 gives the FLRW dust branch",
    }
    negative_branch = {
        "cross_source": "X_minus = det4_metric_minus transport_pf_minus rho_plus",
        "receiver_closure": "dot(X_minus)+3 H_minus (1+w_cross_minus) X_minus=0",
        "transport_condition": (
            "d_t ln(transport_pf_minus)=3 H_plus(1+w_plus)"
            "-3 H_minus(1+w_cross_minus)-d_t ln(det4_metric_minus)"
        ),
        "constant_w_integral": (
            "transport_pf_minus proportional a_plus^(3(1+w_plus)) "
            "a_minus^(-3(1+w_cross_minus)) / det4_metric_minus"
        ),
        "power_law_b_case": (
            "if det4_metric_minus=(a_plus/a_minus)^n_det_minus, "
            "then transport_pf_minus proportional "
            "a_plus^(3(1+w_plus)-n_det_minus) "
            "a_minus^(-3(1+w_cross_minus)+n_det_minus)"
        ),
        "combined_weight": (
            "weight_pf_minus proportional a_plus^(3(1+w_plus)) "
            "a_minus^(-3(1+w_cross_minus))"
        ),
        "dust_limit": "w_plus=w_cross_minus=0 gives the FLRW dust branch",
    }
    blockers = [
        "w_cross_plus/w_cross_minus are not fixed by scalar continuity alone",
        "anisotropic stress must use full tensor transport, not this scalar branch",
        "lapse or non-comoving relative velocity changes the closure equation",
        "Q_cross optical projection remains separate",
        "generic Bianchi closure still requires K_plus/K_minus tensor maps",
    ]
    return {
        "description": "Special FLRW perfect-fluid scalar transport branch.",
        "status": "branch-condition",
        "branch_closed": False,
        "physics_closed": False,
        "notation": notation,
        "assumptions": assumptions,
        "positive_branch": positive_branch,
        "negative_branch": negative_branch,
        "blockers": blockers,
        "verdict": (
            "The perfect-fluid FLRW branch reduces pressure handling to declared "
            "effective cross equations of state. Dust is recovered as a special "
            "case, but pressure does not close the generic tensor map."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi FLRW Perfect-Fluid Transport Branch",
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
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
