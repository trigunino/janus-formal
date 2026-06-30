from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_residual_substitution.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_zero_param_residual_substitution.json")


def build_payload() -> dict:
    k_sources = [
        {
            "sector": "plus",
            "branch": "zero_parameter_normalized_copy",
            "source_copy": "Phi = rho_minus_to_plus normalized by the M15 determinant-source coefficient",
            "k_tensor": "K_plus^{mu nu}=B_minus_to_plus rho_minus_to_plus u_-to+^mu u_-to+^nu",
            "free_parameters": [],
        },
        {
            "sector": "minus",
            "branch": "zero_parameter_normalized_copy",
            "source_copy": "Phi_bar = rho_plus_to_minus normalized by the mirror determinant-source coefficient",
            "k_tensor": "K_minus^{mu nu}=B_plus_to_minus rho_plus_to_minus u_+to-^mu u_+to-^nu",
            "free_parameters": [],
        },
    ]
    residual_substitutions = [
        {
            "target": "R_plus^mu",
            "substitution": (
                "D_plus_nu(K_plus^{mu nu}) with K_plus from zero_parameter_normalized_copy"
            ),
            "obligation_level_expansion": (
                "B_minus_to_plus[D_phi rho_minus, D_L u_-to+, C_plus-minus u u, "
                "rho_minus u u D_plus log B_minus_to_plus, continuity_mismatch_minus_to_plus]"
            ),
            "closes_if": "D_phi terms, D_L terms, connection difference, DlogB, and continuity mismatch vanish",
            "closed": False,
        },
        {
            "target": "R_minus^mu",
            "substitution": (
                "D_minus_nu(K_minus^{mu nu}) with K_minus from zero_parameter_normalized_copy"
            ),
            "obligation_level_expansion": (
                "B_plus_to_minus[D_phi rho_plus, D_L u_+to-, C_minus-plus u u, "
                "rho_plus u u D_minus log B_plus_to_minus, continuity_mismatch_plus_to_minus]"
            ),
            "closes_if": "D_phi terms, D_L terms, connection difference, DlogB, and continuity mismatch vanish",
            "closed": False,
        },
    ]
    remaining_terms = [
        "D_phi transported-density derivatives",
        "D_L transported-velocity/tetrad derivatives",
        "connection difference C_plus-minus/C_minus-plus",
        "DlogB determinant-measure gradients",
        "transported dust continuity mismatch",
    ]
    vanish_status = {term: False for term in remaining_terms}
    all_remaining_terms_vanish = all(vanish_status.values())
    return {
        "description": (
            "Bounded P0 artifact substituting zero-parameter Stueckelberg dust K tensors "
            "into R_plus/R_minus residual targets at obligation level."
        ),
        "status": "zero-param-k-substituted-residuals-open",
        "branch": "zero_parameter_normalized_copy",
        "source_branch": "p0_stueckelberg_minimal_phi_dust_test",
        "fit_used": False,
        "free_parameters": [],
        "k_tensors_listed": True,
        "symbolic_substitution_written": True,
        "obligation_level_only": True,
        "all_remaining_terms_vanish": all_remaining_terms_vanish,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": all_remaining_terms_vanish,
        "prediction_ready": False,
        "k_sources": k_sources,
        "residual_substitutions": residual_substitutions,
        "remaining_terms": remaining_terms,
        "vanish_status": vanish_status,
        "closure_rule": "mark closure true only if every remaining term is proven zero in both residuals",
        "verdict": (
            "The no-fit zero-parameter K_plus/K_minus branch can be substituted into "
            "the residual targets, but D_phi/D_L, connection, DlogB, and continuity "
            "obligations remain open. Therefore closure and prediction readiness stay false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Zero-Parameter Residual Substitution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch: {payload['branch']}",
        f"Fit used: {payload['fit_used']}",
        f"Free parameters: {payload['free_parameters']}",
        f"Symbolic substitution written: {payload['symbolic_substitution_written']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## K Sources",
        "",
    ]
    for row in payload["k_sources"]:
        lines.append(f"- {row['sector']}: `{row['k_tensor']}`")
        lines.append(f"  - source copy: {row['source_copy']}")
        lines.append(f"  - free parameters: {row['free_parameters']}")
    lines.extend(["", "## Residual Substitutions", ""])
    for row in payload["residual_substitutions"]:
        lines.append(f"- {row['target']}: `{row['substitution']}`")
        lines.append(f"  - expansion: `{row['obligation_level_expansion']}`")
        lines.append(f"  - closes if: {row['closes_if']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Remaining Terms", ""])
    lines.extend(f"- {term}: vanishes={payload['vanish_status'][term]}" for term in payload["remaining_terms"])
    lines.extend(["", f"Closure rule: {payload['closure_rule']}", "", f"Verdict: {payload['verdict']}", ""])
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
