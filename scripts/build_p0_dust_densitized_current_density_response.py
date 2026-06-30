from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dust_densitized_current_density_response.md")
JSON_PATH = Path("outputs/reports/p0_dust_densitized_current_density_response.json")


def build_payload() -> dict:
    derivation_rows = [
        {
            "row": "densitized_current_definition",
            "formula": "J^mu = sqrt(-g) N^mu, delta_g J^mu = 0",
            "status": "branch-assumption",
        },
        {
            "row": "current_variation",
            "formula": "delta_g N^mu = -N^mu delta_g log sqrt(-g)",
            "status": "closed-under-fixed-J",
        },
        {
            "row": "measure_variation_covariant",
            "formula": "delta_g log sqrt(-g) = 1/2 g^{alpha beta} delta g_{alpha beta}",
            "status": "closed-algebraic",
        },
        {
            "row": "density_variation",
            "formula": "delta_g rho = -1/2 rho (u^alpha u^beta + g^{alpha beta}) delta g_{alpha beta}",
            "status": "closed-under-fixed-J",
        },
        {
            "row": "convention_warning",
            "formula": "sign/form changes if varying delta g^{mu nu} instead of delta g_{mu nu}",
            "status": "index-convention-required",
        },
        {
            "row": "janus_pullback_warning",
            "formula": "pulled J^mu needs B_4vol/J_phi convention before use in K_plus/K_minus",
            "status": "separate-branch-required",
        },
    ]
    return {
        "description": "Densitized-current branch for dust density metric response.",
        "status": "densitized-current-density-response-closed-branch-only",
        "derivation_rows": derivation_rows,
        "densitized_current_branch_closed": True,
        "fixed_vector_current_branch_closed": False,
        "janus_pullback_branch_closed": False,
        "pullback_density_response_bridge_available": True,
        "index_convention_locked": False,
        "full_dust_delta_g_t_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "delta_g rho is closed for fixed densitized current J. It still cannot be "
            "used for Janus K unless the pullback measure convention is selected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Densitized Current Density Response",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Densitized current branch closed: {payload['densitized_current_branch_closed']}",
        f"Fixed vector current branch closed: {payload['fixed_vector_current_branch_closed']}",
        f"Janus pullback branch closed: {payload['janus_pullback_branch_closed']}",
        f"Pullback density response bridge available: {payload['pullback_density_response_bridge_available']}",
        f"Index convention locked: {payload['index_convention_locked']}",
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
