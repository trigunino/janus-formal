from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dust_fixed_current_density_response.md")
JSON_PATH = Path("outputs/reports/p0_dust_fixed_current_density_response.json")


def build_payload() -> dict:
    derivation_rows = [
        {
            "row": "fixed_current_definition",
            "formula": "N^mu = rho u^mu, delta_g N^mu = 0",
            "status": "branch-assumption",
        },
        {
            "row": "density_norm",
            "formula": "rho^2 = -g_{mu nu} N^mu N^nu",
            "status": "closed-algebraic",
        },
        {
            "row": "density_variation",
            "formula": "delta_g rho = -1/2 rho u^mu u^nu delta g_{mu nu}",
            "status": "closed-under-fixed-current",
        },
        {
            "row": "parallel_velocity_response",
            "formula": "u_mu delta_g u^mu = -1/2 u^mu u^nu delta g_{mu nu}",
            "status": "closed-under-fixed-current",
        },
        {
            "row": "transverse_velocity_response",
            "formula": "h^mu_nu delta_g u^nu = 0",
            "status": "branch-assumption-not-janus-derived",
        },
        {
            "row": "densitized_current_warning",
            "formula": "if J^mu=sqrt(-g)N^mu is fixed, delta_g rho receives an extra measure term",
            "status": "separate-branch-required",
        },
    ]
    return {
        "description": "Controlled fixed-current branch for the dust density metric response.",
        "status": "fixed-current-density-response-closed-branch-only",
        "derivation_rows": derivation_rows,
        "fixed_vector_current_branch_closed": True,
        "densitized_current_branch_closed": False,
        "densitized_current_density_response_available": True,
        "janus_pullback_branch_closed": False,
        "transverse_velocity_response_derived": False,
        "full_dust_delta_g_t_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "delta_g rho is closed only for the fixed non-densitized current branch. "
            "Janus/pullback dust still needs its own current convention."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Fixed Current Density Response",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Fixed vector current branch closed: {payload['fixed_vector_current_branch_closed']}",
        f"Densitized current branch closed: {payload['densitized_current_branch_closed']}",
        f"Densitized current density response available: {payload['densitized_current_density_response_available']}",
        f"Janus pullback branch closed: {payload['janus_pullback_branch_closed']}",
        f"Transverse velocity response derived: {payload['transverse_velocity_response_derived']}",
        f"Full dust delta_g T closed: {payload['full_dust_delta_g_t_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Rows",
        "",
    ]
    for row in payload["derivation_rows"]:
        lines.append(f"- {row['row']}: `{row['formula']}` ({row['status']})")
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
